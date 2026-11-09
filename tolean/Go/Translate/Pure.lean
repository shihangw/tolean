import tolean.Go.IR
import tolean.Go.Spec.Eval

/-!
The part of the Go translator that builds the Tolean IR, for pure functions.

A pure function here takes and returns `int`, `int64`, `bool` and `string`
values, and calls only pure functions that this part has already
translated. Its body may declare and assign locals, use `+=`, `-=`, `*=`,
`++` and `--`, test with `if` and `else`, and return. Integer arithmetic
wraps through `Go.wrap64`, as Go's does.

The translator is a total function, so that Lean can reason about it.
`translate_sound` in `tolean/Go/Proof/Package.lean` proves that every
function it writes means what the source means: when the IR evaluator gives
a value for a call, the interpreter in `tolean/Go/Spec/Eval.lean` gives the
same value. `tolean/Go/Translate.lean` uses this part for every pure function
that it accepts, and its older string translation for everything else.

The translator gives each expression the type that Go gives it, and it
refuses what it cannot type exactly. An integer literal is an untyped
constant, which takes the type of the other operand. The translator refuses
an operator on two untyped constants. Go evaluates such an operator exactly,
with no wrapping. In Go, `9223372036854775807 + 1 > 0` is true, but the
wrapping arithmetic of the output would make it false.
-/
namespace tolean.Go.Pure

open tolean.Go.Syntax
open tolean.Go.Eval (BinOp AssignKind)

/-- A Go type of the subset. `untyped` is the type of an integer constant
that no typed value has fixed yet. -/
inductive Ty where
  | int | int64 | bool | string | untyped
deriving DecidableEq, Repr, Inhabited

def Ty.lean : Ty → IR.Ty
  | .bool => .bool
  | .string => .string
  | .int | .int64 | .untyped => .int

def Ty.isInt : Ty → Bool
  | .int | .int64 | .untyped => true
  | .bool | .string => false

/-- The type that two operands share: the same type, or an untyped constant
and an integer type. Two untyped constants share none, because the subset
leaves out constant expressions. -/
def Ty.unify : Ty → Ty → Option Ty
  | .untyped, .untyped => none
  | .untyped, t => if t.isInt then some t else none
  | t, .untyped => if t.isInt then some t else none
  | a, b => if a = b then some a else none

/-- A value of type `source` can stand where Go expects a `target`. -/
def Ty.fits (source target : Ty) : Bool := source.unify target == some target

/-- The type of a local that `:=` declares: an untyped constant becomes an
`int`. -/
def Ty.typed : Ty → Ty
  | .untyped => .int
  | t => t

structure Local where
  name : String
  type : Ty
deriving Inhabited

/-- The locals in scope, in the order they were declared. The translator never
declares a name twice, so the order does not change a lookup. -/
abbrev Env := List Local

def Env.lookup (env : Env) (name : String) : Option Local := env.find? (·.name == name)

def Env.has (env : Env) (name : String) : Bool := (env.lookup name).isSome

/-- What a call of a translated function needs to know. -/
structure FnSig where
  name : String
  params : List Ty
  result : Ty
deriving Inhabited

structure Ctx where
  program : Eval.Program
  /-- The functions translated so far. A function may call only these, so
  that the output declares each function before its callers. -/
  known : List FnSig

abbrev TM := Except String

def reject {A : Type} (sp : Span) (reason : String) : TM A :=
  throw s!"{sp.start.line}:{sp.start.col}: {reason}"

/-- The bound on the depth of an expression. -/
def exprFuel : Nat := 256

/-- The bound on the depth of the statements of a function. -/
def stmtFuel : Nat := 4096

/-- Words that Lean reads as keywords or that the output of the older string
translation uses, so that a Go name must be quoted as `«name»` to be one.
Both paths of the translator read this list. -/
def leanKeywords : List String :=
  ["at", "by", "do", "then", "else", "if", "match", "with", "let", "have", "show", "from",
   "in", "fun", "end", "open", "namespace", "section", "return", "mut", "for", "unless",
   "where", "instance", "structure", "class", "theorem", "def", "axiom", "variable",
   "universe", "Type", "Prop", "Sort", "import", "deriving", "extends", "calc", "try",
   "catch", "finally", "break", "continue", "nomatch", "nofun", "macro", "syntax", "local",
   "private", "protected", "partial", "unsafe", "noncomputable", "example", "abbrev",
   "opaque", "inductive", "export", "attribute", "notation", "this", "rest", "pure",
   "mutual", "termination_by", "decreasing_by", "suffices", "nonrec", "omit", "include"]

/-- Names that the output of this part may not bind. They are the names that
would need quotes, the Lean names that the output uses, and Go's predeclared
names, whose meaning a local would change. This part never quotes a name. It
refuses the function instead, and the older string translation writes it. -/
def takenNames : List String :=
  leanKeywords ++ tolean.IR.leanReserved ++ IR.leanNames.map (·.1) ++
    ["tolean", "true", "false", "int", "int64", "bool", "string", "nil", "_", "init"]

def nameOK (name : String) : Bool := !takenNames.contains name

/-- The type that a type expression names: a predeclared type, unless the
package declares the name. -/
def resolveType (ctx : Ctx) : Expr → Option Ty
  | .ident _ name =>
    if ctx.program.names.contains name then none
    else match name with
      | "int" => some .int
      | "int64" => some .int64
      | "bool" => some .bool
      | "string" => some .string
      | _ => none
  | _ => none

/-- The zero value of a type, as code. -/
def zeroCode : Ty → IR.Expr
  | .bool => .bool false
  | .string => .string ""
  | .int | .int64 | .untyped => .int 0

/-! ### Expressions -/

/-- `a op b` on integers, which wraps. -/
def arith (sp : Span) (op : tolean.IR.IntOp) (a : IR.Expr) (ta : Ty) (b : IR.Expr) (tb : Ty) :
    TM (IR.Expr × Ty) :=
  match ta.unify tb with
  | some t => if t.isInt then pure (.wrap64 (.intOp op a b), t) else reject sp "this operator needs integers"
  | none => reject sp "the operands do not have one integer type"

/-- `a < b` and the other orders, on integers. -/
def compare (sp : Span) (op : tolean.IR.Order) (a : IR.Expr) (ta : Ty) (b : IR.Expr) (tb : Ty) :
    TM (IR.Expr × Ty) :=
  match ta.unify tb with
  | some t => if t.isInt then pure (.decide (.order op a b), .bool) else reject sp "the subset orders only integers"
  | none => reject sp "the operands do not have one integer type"

/-- A binary operator on translated operands. -/
def translateBinary (sp : Span) (o : BinOp) (a : IR.Expr) (ta : Ty) (b : IR.Expr) (tb : Ty) :
    TM (IR.Expr × Ty) :=
  match o with
  | .land => if ta = .bool ∧ tb = .bool then pure (.and a b, .bool) else reject sp "&& needs booleans"
  | .lor => if ta = .bool ∧ tb = .bool then pure (.or a b, .bool) else reject sp "|| needs booleans"
  | .add =>
    if ta = .string ∧ tb = .string then pure (.append a b, .string) else arith sp .add a ta b tb
  | .sub => arith sp .sub a ta b tb
  | .mul => arith sp .mul a ta b tb
  | .lt => compare sp .lt a ta b tb
  | .le => compare sp .le a ta b tb
  | .gt => compare sp .gt a ta b tb
  | .ge => compare sp .ge a ta b tb
  | .eq =>
    match ta.unify tb with
    | some _ => pure (.decide (.eq a b), .bool)
    | none => reject sp "the operands do not have one type"
  | .ne =>
    match ta.unify tb with
    | some _ => pure (.decide (.ne a b), .bool)
    | none => reject sp "the operands do not have one type"

/-- The arguments fit the parameters, one for one. -/
def argsFit (codes : List (IR.Expr × Ty)) (params : List Ty) : Bool :=
  codes.length == params.length && (codes.zip params).all fun (c, p) => c.2.fits p

mutual

/-- The code of an expression, and its type. -/
def translateExpr (ctx : Ctx) (env : Env) : Nat → Expr → TM (IR.Expr × Ty)
  | 0, e => reject e.span "the expression is nested too deeply"
  | fuel + 1, e =>
    match e with
    | .ident sp name =>
      match env.lookup name with
      | some l => pure (.var name, l.type)
      | none =>
        match Eval.predeclared ctx.program name with
        | some (.bool b) => pure (.bool b, .bool)
        | _ => reject sp s!"unknown name '{name}'"
    | .lit sp .int raw =>
      match Eval.intLit? raw with
      | some n => if n < 2 ^ 63 then pure (.int n, .untyped) else reject sp "the literal does not fit in int64"
      | none => reject sp "this integer literal is not supported"
    | .lit sp .string raw =>
      match Eval.stringLit? raw with
      | some s => pure (.string s, .string)
      | none => reject sp "this string literal has an escape that the subset leaves out"
    | .paren _ inner => translateExpr ctx env fuel inner
    | .unary sp op a => do
      let (c, t) ← translateExpr ctx env fuel a
      match op with
      | "-" => if t.isInt then pure (.wrap64 (.neg c), t) else reject sp "- needs an integer"
      | "!" => if t = .bool then pure (.not c, .bool) else reject sp "! needs a boolean"
      | _ => reject sp s!"the operator '{op}' is not supported"
    | .binary sp op l r => do
      let some o := BinOp.ofString? op | reject sp s!"the operator '{op}' is not supported"
      let (a, ta) ← translateExpr ctx env fuel l
      let (b, tb) ← translateExpr ctx env fuel r
      translateBinary sp o a ta b tb
    | .call sp (.ident _ f) args false => do
      if env.has f then reject sp s!"'{f}' is a local, not a function"
      let some sig := ctx.known.find? (·.name == f) | reject sp s!"'{f}' is not a pure function translated before this one"
      let codes ← translateArgs ctx env fuel args
      unless argsFit codes sig.params do reject sp "the arguments do not fit the parameters"
      pure (.call ⟨"", f⟩ (codes.map (·.1)), sig.result)
    | e => reject e.span "this expression is not supported"

def translateArgs (ctx : Ctx) (env : Env) : Nat → List Expr → TM (List (IR.Expr × Ty))
  | _, [] => pure []
  | 0, e :: _ => reject e.span "the expression is nested too deeply"
  | fuel + 1, e :: es => do
    return (← translateExpr ctx env fuel e) :: (← translateArgs ctx env fuel es)

end

/-! ### Statements -/

/-- What the end of a statement list gives: the function's value, or the
locals that a branch changes. -/
inductive Tail where
  | ret (result : Ty)
  | state (names : List String)

def blockStatements : Stmt → List Stmt
  | .block _ ss => ss
  | s => [s]

/-- The statements of an `else`, which is a block or another `if`. -/
def elseStatements : Option Stmt → List Stmt
  | some e => blockStatements e
  | none => []

mutual

/-- The names that a statement may assign. -/
def stmtChanges : Stmt → List String
  | .assign _ _ lhs _ => lhs.filterMap fun
    | .ident _ n => some n
    | _ => none
  | .incDec _ _ (.ident _ n) => [n]
  | .block _ ss => changesList ss
  | .ifStmt _ _ _ t e => stmtChanges t ++ changesOption e
  | _ => []

def changesList : List Stmt → List String
  | [] => []
  | s :: ss => stmtChanges s ++ changesList ss

def changesOption : Option Stmt → List String
  | none => []
  | some s => stmtChanges s

end

mutual

/-- The statement holds a `return`. -/
def hasReturn : Stmt → Bool
  | .ret .. => true
  | .block _ ss => anyReturn ss
  | .ifStmt _ _ _ t e => hasReturn t || optionReturn e
  | _ => false

def anyReturn : List Stmt → Bool
  | [] => false
  | s :: ss => hasReturn s || anyReturn ss

def optionReturn : Option Stmt → Bool
  | none => false
  | some s => hasReturn s

end

/-- The locals of `env` that the statements may assign, in the order of
`env`. -/
def changedNames (ss : List Stmt) (env : Env) : List String :=
  (env.filter fun l => (changesList ss).contains l.name).map (·.name)

/-- Declare a new local. The translator refuses a name that is in scope
already, so a lookup never depends on the order of the scope. -/
def declare (env : Env) (sp : Span) (name : String) (type : Ty) : TM Env :=
  if env.has name then reject sp s!"'{name}' is declared already; the subset does not shadow"
  else if !nameOK name then reject sp s!"the name '{name}' is reserved"
  else pure (env ++ [⟨name, type⟩])

mutual

/-- The body for the statements `ss`, which end as `tail` says. -/
def translateStmts (ctx : Ctx) (env : Env) (tail : Tail) : Nat → List Stmt → TM IR.Body
  | 0, _ => throw "the statements are nested too deeply"
  | _ + 1, [] =>
    match tail with
    | .ret _ => throw "the function can end without a return"
    | .state names => pure (.state names)
  | fuel + 1, st :: rest =>
    match st with
    | .ret sp [e] => do
      let .ret result := tail | reject sp "only a branch that always returns may return"
      unless rest.isEmpty do reject sp "the code after return is unreachable"
      let (c, t) ← translateExpr ctx env exprFuel e
      unless t.fits result do reject sp "the value does not have the result type"
      pure (.value c)
    | .assign sp op [.ident _ x] [e] => do
      let some kind := AssignKind.ofString? op | reject sp s!"the operator '{op}' is not supported"
      let (c, t) ← translateExpr ctx env exprFuel e
      match kind with
      | .define =>
        let env' ← declare env sp x t.typed
        return .let x c (← translateStmts ctx env' tail fuel rest)
      | .assign =>
        let some l := env.lookup x | reject sp s!"unknown local '{x}'"
        unless t.fits l.type do reject sp "the value does not have the type of the local"
        return .let x c (← translateStmts ctx env tail fuel rest)
      | .compound o =>
        let some l := env.lookup x | reject sp s!"unknown local '{x}'"
        let (c', t') ← translateBinary sp o (.var x) l.type c t
        unless t' = l.type do reject sp "the value does not have the type of the local"
        return .let x c' (← translateStmts ctx env tail fuel rest)
    | .incDec sp op (.ident _ x) => do
      let some o := Eval.incDecOp? op | reject sp s!"the operator '{op}' is not supported"
      let some l := env.lookup x | reject sp s!"unknown local '{x}'"
      let (c', t') ← translateBinary sp o (.var x) l.type (.int 1) .untyped
      unless t' = l.type do reject sp "++ and -- need an integer local"
      return .let x c' (← translateStmts ctx env tail fuel rest)
    | .decl sp (.mk _ "var" [.value _ [x] (some te) values]) => do
      let some t := resolveType ctx te | reject sp "the subset has no such type"
      let c ← match values with
        | [e] => do
          let (c, t') ← translateExpr ctx env exprFuel e
          unless t'.fits t do reject sp "the value does not have the declared type"
          pure c
        | [] => pure (zeroCode t)
        | _ => reject sp "declare one variable at a time"
      let env' ← declare env sp x t
      return .let x c (← translateStmts ctx env' tail fuel rest)
    | .ifStmt sp none c t els => translateIf ctx env tail fuel sp c t els rest
    | _ => reject st.span "this statement is not supported"

/-- `if c { … } else …`, then `rest`. When a branch returns, the code after
the `if` joins the other branch, so the `if` must have no `else` unless
nothing follows it. Otherwise the branches give the locals they change, and
`rest` follows. -/
def translateIf (ctx : Ctx) (env : Env) (tail : Tail) : Nat → Span → Expr → Stmt →
    Option Stmt → List Stmt → TM IR.Body
  | 0, sp, _, _, _, _ => reject sp "the statements are nested too deeply"
  | fuel + 1, sp, c, t, els, rest => do
    let (cond, ct) ← translateExpr ctx env exprFuel c
    unless ct = .bool do reject sp "a condition must be a boolean"
    let thenSS := blockStatements t
    let elseSS := elseStatements els
    if anyReturn (thenSS ++ elseSS) then
      let .ret _ := tail | reject sp "only a branch that always returns may return"
      if els.isSome && !rest.isEmpty then
        reject sp "when a branch returns and the if has an else, nothing may follow the if"
      let whenTrue ← translateStmts ctx env tail fuel thenSS
      let whenFalse ← translateStmts ctx env tail fuel (elseSS ++ rest)
      return .ite cond whenTrue whenFalse
    else
      let names := changedNames (thenSS ++ elseSS) env
      if names.isEmpty then reject sp "an if that does not return must change a local"
      let whenTrue ← translateStmts ctx env (.state names) fuel thenSS
      let whenFalse ← translateStmts ctx env (.state names) fuel elseSS
      return .letState names (.ite cond whenTrue whenFalse) (← translateStmts ctx env tail fuel rest)

end

/-! ### Functions -/

/-- The parameters and their types. A parameter without a name, as in
`func f(int) int`, still takes an argument, so this part refuses it and the
older string translation writes the function. -/
def paramList (ctx : Ctx) : List Field → Option (List (String × Ty))
  | [] => some []
  | .mk _ [] _ _ :: _ => none
  | .mk _ names te _ :: rest => do
    let t ← resolveType ctx te
    return names.map (·, t) ++ (← paramList ctx rest)

/-- A pure function: its declaration in the output, and its signature. -/
def translateFunc (ctx : Ctx) : Decl → TM (IR.Decl × FnSig)
  | .func sp none name params (some [.mk _ [] rt none]) (.block _ body) => do
    unless nameOK name do reject sp s!"the name '{name}' is reserved"
    let some ps := paramList ctx params | reject sp "a parameter has a type outside the subset"
    let some result := resolveType ctx rt | reject sp "the result has a type outside the subset"
    unless (ps.map (·.1)).Nodup do reject sp "two parameters have one name"
    unless ps.all (nameOK ·.1) do reject sp "a parameter has a reserved name"
    let env : Env := ps.map fun (n, t) => ⟨n, t⟩
    let b ← translateStmts ctx env (.ret result) stmtFuel body
    return (.function name (ps.map fun (n, t) => (n, t.lean)) result.lean b,
      ⟨name, ps.map (·.2), result⟩)
  | .func sp .. => reject sp "only a function with one result and no receiver can be pure"
  | .gen _ => throw "not a function"

/-- The function `name` of the declarations, as a call of `name` finds it. -/
def findFunc (decls : List Decl) (name : String) : Option Decl :=
  decls.find? fun
    | .func _ none n .. => n == name && !(n == "init" || n == "_")
    | _ => false

/-- Translate the functions named in `order`, in that order, after those in
`acc`. A function that the translator refuses is left out, and so is any
function that calls it. -/
def translateFuncsFrom (decls : List Decl) : List String → List (IR.Decl × FnSig) →
    List (IR.Decl × FnSig)
  | [], acc => acc
  | n :: ns, acc =>
    if acc.any (·.2.name == n) then translateFuncsFrom decls ns acc
    else match findFunc decls n with
      | none => translateFuncsFrom decls ns acc
      | some d =>
        match translateFunc ⟨Eval.program decls, acc.map (·.2)⟩ d with
        | .ok r => if r.2.name == n then translateFuncsFrom decls ns (acc ++ [r])
          else translateFuncsFrom decls ns acc
        | .error _ => translateFuncsFrom decls ns acc

/-- The pure functions of a package that the translator accepts, from the
declarations of all its files, in the order `order`. -/
def translateFuncs (decls : List Decl) (order : List String) : List (IR.Decl × FnSig) :=
  translateFuncsFrom decls order []

end tolean.Go.Pure
