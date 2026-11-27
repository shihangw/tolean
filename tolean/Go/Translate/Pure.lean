import tolean.Go.IR
import tolean.Go.Spec.Eval

/-!
The part of the Go translator that builds the Tolean IR, for pure functions.

A pure function here takes and returns `int`, `int64`, `bool` and `string`
values, and calls only pure functions that this part has already
translated. Its body may declare and assign locals, use `+=`, `-=`, `*=`,
`/=`, `%=`, `++` and `--`, test with `if`, `else` and `switch`, and return.
An `if` or a `switch` may have an init statement. Integer arithmetic wraps
through `Go.wrap64`, as Go's does.

Integer `/` and `%` are `Int.tdiv` and `Int.tmod`. Go panics when the divisor
is zero, and Lean divides by zero without a panic, so a statement that
divides first tests its divisors. When one of them is zero, the function
throws the message of Go's panic. A function that can panic returns
`Except String T` rather than `T`. A call of it must stand alone on the right
of `:=`, `=` or `var`, or after `return`, and the output binds it with
`>>=`, so that its panic is the caller's panic.

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
  /-- The function can panic, so its output returns an `Except`. -/
  panics : Bool := false
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

/-! ### Division -/

/-- The divisor `b`, unless it is an integer literal other than zero, which
needs no test. -/
def tested : IR.Expr → List IR.Expr
  | .int n => if n = 0 then [.int n] else []
  | b => [b]

/-- The divisors of the divisions in `c`, in no particular order. A statement
that evaluates `c` panics in Go exactly when one of them is zero, because the
translator refuses a division that Go might not evaluate: one in the right
operand of `&&` or `||`. -/
def divisors : IR.Expr → List IR.Expr
  | .division _ a b => divisors a ++ divisors b ++ tested b
  | .not a => divisors a
  | .neg a => divisors a
  | .decide a => divisors a
  | .intOp _ a b => divisors a ++ divisors b
  | .order _ a b => divisors a ++ divisors b
  | .eq a b => divisors a ++ divisors b
  | .ne a b => divisors a ++ divisors b
  | .and a b => divisors a ++ divisors b
  | .or a b => divisors a ++ divisors b
  | .call _ args => divisorsList args
  | .ext _ args => divisorsList args
  | _ => []
where
  divisorsList : List IR.Expr → List IR.Expr
    | [] => []
    | e :: es => divisors e ++ divisorsList es

/-- `decide (d = 0)`. -/
def isZero (d : IR.Expr) : IR.Expr := .decide (.eq d (.int 0))

/-- Some divisor of `ds` is zero, as a `Bool`. -/
def anyZero : List IR.Expr → IR.Expr
  | [] => .bool false
  | [d] => isZero d
  | d :: ds => .or (isZero d) (anyZero ds)

/-- The test before a statement whose expressions divide by `ds`: `d = 0` for
one divisor, and a `||` of `decide (d = 0)` for more. -/
def zeroTest : List IR.Expr → IR.Expr
  | [d] => .eq d (.int 0)
  | ds => anyZero ds

/-- The message of Go's panic for a division by zero. -/
def panicCode : IR.Expr := .string "runtime error: integer divide by zero"

/-- `body`, after a test of the divisors of `c`, which `body` evaluates
first. When one of them is zero, the output evaluates `c` and throws Go's
panic. `c` divides by zero then without a panic, as Lean does, and its value
is unused. The output evaluates it so that the evaluator reaches the same
expressions as the interpreter, which panics only when it reaches the
division. A statement that does not divide keeps `body` as it is. -/
def guarded (c : IR.Expr) (body : IR.Body) : IR.Body :=
  if (divisors c).isEmpty then body
  else .ite (zeroTest (divisors c)) (.let "_" c (.throw panicCode)) body

/-- The code of an untyped constant is zero. Such a constant is a literal,
possibly negated, because the translator refuses an operator on two
constants. -/
def constZero : IR.Expr → Bool
  | .int 0 => true
  | .ext .wrap64 [.neg a] => constZero a
  | _ => false

/-- `a / b` and `a % b` on integers. A constant zero divisor is an error in
Go (Go specification, "Integer operators"), so the translator refuses it. -/
def divide (sp : Span) (op : tolean.IR.Division) (a : IR.Expr) (ta : Ty) (b : IR.Expr) (tb : Ty) :
    TM (IR.Expr × Ty) :=
  match ta.unify tb with
  | some t =>
    if !t.isInt then reject sp "this operator needs integers"
    else if tb = .untyped && constZero b then reject sp "division by the constant zero"
    else match op with
      | .tdiv => pure (.wrap64 (.division .tdiv a b), t)
      | .tmod => pure (.division .tmod a b, t)
  | none => reject sp "the operands do not have one integer type"

/-- A binary operator on translated operands. -/
def translateBinary (sp : Span) (o : BinOp) (a : IR.Expr) (ta : Ty) (b : IR.Expr) (tb : Ty) :
    TM (IR.Expr × Ty) :=
  match o with
  | .land =>
    if !(divisors b).isEmpty then reject sp "the right operand of && may not divide"
    else if ta = .bool ∧ tb = .bool then pure (.and a b, .bool) else reject sp "&& needs booleans"
  | .lor =>
    if !(divisors b).isEmpty then reject sp "the right operand of || may not divide"
    else if ta = .bool ∧ tb = .bool then pure (.or a b, .bool) else reject sp "|| needs booleans"
  | .quo => divide sp .tdiv a ta b tb
  | .rem => divide sp .tmod a ta b tb
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
      if sig.panics then
        reject sp s!"'{f}' can panic, so a call of it must stand alone after :=, =, var or return"
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

/-- A statement that binds a call of a function that can panic: `return`,
`x := …`, `x = …` or `var x T = …`. -/
inductive BindForm where
  | ret
  | define (x : String)
  | assign (x : String)
  | var (x : String) (type : Expr)

/-- `e` is a call `f(args)` of a function `f` that can panic: `f`, the
arguments and the signature of `f`. -/
def panicCallee? (ctx : Ctx) (env : Env) : Expr → Option (String × List Expr × FnSig)
  | .call _ (.ident _ f) args false =>
    if env.has f then none
    else match ctx.known.find? (·.name == f) with
      | some sig => if sig.panics then some (f, args, sig) else none
      | none => none
  | _ => none

/-- `st` is a call of a function `f` that can panic, `f(args)`, in a form of
`BindForm`: the form, its span, `f`, the arguments and the signature of `f`. -/
def bindCall? (ctx : Ctx) (env : Env) (st : Stmt) :
    Option (BindForm × Span × String × List Expr × FnSig) :=
  match st with
  | .ret sp [e] => (panicCallee? ctx env e).map fun (f, args, sig) => (.ret, sp, f, args, sig)
  | .assign sp ":=" [.ident _ x] [e] =>
    (panicCallee? ctx env e).map fun (f, args, sig) => (.define x, sp, f, args, sig)
  | .assign sp "=" [.ident _ x] [e] =>
    (panicCallee? ctx env e).map fun (f, args, sig) => (.assign x, sp, f, args, sig)
  | .decl sp (.mk _ "var" [.value _ [x] (some te) [e]]) =>
    (panicCallee? ctx env e).map fun (f, args, sig) => (.var x te, sp, f, args, sig)
  | _ => none

/-- The name that `return f(…)` binds the value of the call to. The body
after the bind only returns it, so it may hide a local. -/
def resultName : String := "result"

/-- What the end of a statement list gives: the function's value, or the
locals that a branch changes. A function that can panic (`monadic`) returns
`pure` of its value. -/
inductive Tail where
  | ret (result : Ty) (monadic : Bool)
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
  | .ifStmt _ init _ t e => changesOption init ++ stmtChanges t ++ changesOption e
  | .switchStmt _ init _ _ cs => changesOption init ++ changesClauses cs
  | _ => []

def changesList : List Stmt → List String
  | [] => []
  | s :: ss => stmtChanges s ++ changesList ss

def changesOption : Option Stmt → List String
  | none => []
  | some s => stmtChanges s

def changesClauses : List CaseClause → List String
  | [] => []
  | .mk _ _ body :: cs => changesList body ++ changesClauses cs

end

mutual

/-- The statement holds a `return`. -/
def hasReturn : Stmt → Bool
  | .ret .. => true
  | .block _ ss => anyReturn ss
  | .ifStmt _ _ _ t e => hasReturn t || optionReturn e
  | .switchStmt _ _ _ _ cs => clausesReturn cs
  | _ => false

def anyReturn : List Stmt → Bool
  | [] => false
  | s :: ss => hasReturn s || anyReturn ss

def optionReturn : Option Stmt → Bool
  | none => false
  | some s => hasReturn s

def clausesReturn : List CaseClause → Bool
  | [] => false
  | .mk _ _ body :: cs => anyReturn body || clausesReturn cs

end

/-! ### Switch statements

The translator writes an expression switch as the chain of `if` statements
that means the same. `Proof/Switch.lean` proves that the interpreter gives the
chain the meaning that it gives the switch. -/

/-- The test of one case expression `e`: `x == e` for the switch expression
`x`, and `e` itself in a switch without one. -/
def caseTest (sp : Span) : Option Expr → Expr → Expr
  | none, e => e
  | some x, e => .binary sp "==" x e

/-- The test of a case clause, which holds when one of its expressions
matches: `x == a || x == b`. None for a clause without expressions. -/
def caseCond (sp : Span) (tag : Option Expr) : List Expr → Option Expr
  | [] => none
  | e :: es =>
    match caseCond sp tag es with
    | none => some (caseTest sp tag e)
    | some r => some (.binary sp "||" (caseTest sp tag e) r)

/-- The chain of `if` statements for the clauses of a switch. `dflt` is the
`default` clause seen so far, which runs when no case matches. Each clause
body is a block, as it is in Go. -/
def switchChain (tag : Option Expr) : Option (Span × List Stmt) → List CaseClause → Option Stmt
  | none, [] => none
  | some (sp, body), [] => some (.block sp body)
  | _, .mk sp none body :: rest => switchChain tag (some (sp, body)) rest
  | dflt, .mk sp (some es) body :: rest =>
    match caseCond sp tag es with
    | none => switchChain tag dflt rest
    | some c => some (.ifStmt sp none c (.block sp body) (switchChain tag dflt rest))

/-- Some clause has a case expression, so that the chain evaluates the switch
expression, as the switch does. -/
def hasCase : List CaseClause → Bool
  | [] => false
  | .mk _ (some (_ :: _)) _ :: _ => true
  | _ :: cs => hasCase cs

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
    | .ret .. => throw "the function can end without a return"
    | .state names => pure (.state names)
  | fuel + 1, st :: rest =>
    match bindCall? ctx env st with
    | some (form, sp, f, args, sig) => do
      let codes ← translateArgs ctx env exprFuel args
      unless argsFit codes sig.params do reject sp "the arguments do not fit the parameters"
      let cs := codes.map (·.1)
      let ref : DeclRef := ⟨"", f⟩
      -- The test of the arguments' divisors evaluates the arguments, but not
      -- the call: the callee could panic for the values that a zero divisor
      -- gives in Lean, and the panic must be the division's.
      let bound (x : String) (rb : IR.Body) : IR.Body := guarded (.ext .args cs) (.bind x ref cs rb)
      match form with
      | .ret =>
        let .ret result monadic := tail | reject sp "only a branch that always returns may return"
        unless rest.isEmpty do reject sp "the code after return is unreachable"
        unless sig.result.fits result do reject sp "the value does not have the result type"
        let r := IR.Expr.var resultName
        pure (bound resultName (.value (if monadic then IR.Expr.pure r else r)))
      | .define x =>
        let env' ← declare env sp x sig.result.typed
        return bound x (← translateStmts ctx env' tail fuel rest)
      | .assign x =>
        let some l := env.lookup x | reject sp s!"unknown local '{x}'"
        unless sig.result.fits l.type do reject sp "the value does not have the type of the local"
        return bound x (← translateStmts ctx env tail fuel rest)
      | .var x te =>
        let some t := resolveType ctx te | reject sp "the subset has no such type"
        unless sig.result.fits t do reject sp "the value does not have the declared type"
        let env' ← declare env sp x t
        return bound x (← translateStmts ctx env' tail fuel rest)
    | none =>
    match st with
    | .ret sp [e] => do
      let .ret result monadic := tail | reject sp "only a branch that always returns may return"
      unless rest.isEmpty do reject sp "the code after return is unreachable"
      let (c, t) ← translateExpr ctx env exprFuel e
      unless t.fits result do reject sp "the value does not have the result type"
      pure (guarded c (.value (if monadic then IR.Expr.pure c else c)))
    | .assign sp op [.ident _ x] [e] => do
      let some kind := AssignKind.ofString? op | reject sp s!"the operator '{op}' is not supported"
      let (c, t) ← translateExpr ctx env exprFuel e
      match kind with
      | .define =>
        let env' ← declare env sp x t.typed
        return guarded c (.let x c (← translateStmts ctx env' tail fuel rest))
      | .assign =>
        let some l := env.lookup x | reject sp s!"unknown local '{x}'"
        unless t.fits l.type do reject sp "the value does not have the type of the local"
        return guarded c (.let x c (← translateStmts ctx env tail fuel rest))
      | .compound o =>
        let some l := env.lookup x | reject sp s!"unknown local '{x}'"
        let (c', t') ← translateBinary sp o (.var x) l.type c t
        unless t' = l.type do reject sp "the value does not have the type of the local"
        return guarded c' (.let x c' (← translateStmts ctx env tail fuel rest))
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
      return guarded c (.let x c (← translateStmts ctx env' tail fuel rest))
    | .ifStmt sp none c t els => translateIf ctx env tail fuel sp c t els rest
    -- `if s; c { … }` is the block `{ s; if c { … } }`.
    | .ifStmt sp (some s) c t els =>
      translateStmts ctx env tail fuel (.block sp [s, .ifStmt sp none c t els] :: rest)
    -- A switch is a chain of `if` statements, inside a block after its init
    -- statement.
    | .switchStmt sp init tag bsp clauses => do
      if tag.isSome && !hasCase clauses then
        reject sp "a switch with an expression needs a case"
      let some chain := switchChain tag none clauses | reject sp "a switch needs a clause"
      let st' := match init with
        | none => chain
        | some s => .block bsp [s, chain]
      translateStmts ctx env tail fuel (st' :: rest)
    -- A block: what it declares goes out of scope at its end. When it
    -- returns, it must end the function. Otherwise it gives the locals that it
    -- changes, as a branch does.
    | .block sp body => do
      if anyReturn body then
        let .ret .. := tail | reject sp "only a branch that always returns may return"
        unless rest.isEmpty do
          reject sp "a block, or an if or switch with an init statement, that returns must end the function"
        translateStmts ctx env tail fuel body
      else
        let names := changedNames body env
        if names.isEmpty then reject sp "a block that does not return must change a local"
        let inner ← translateStmts ctx env (.state names) fuel body
        return .letState names inner (← translateStmts ctx env tail fuel rest)
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
      let .ret .. := tail | reject sp "only a branch that always returns may return"
      if els.isSome && !rest.isEmpty then
        reject sp "when a branch returns and the if has an else, nothing may follow the if"
      let whenTrue ← translateStmts ctx env tail fuel thenSS
      let whenFalse ← translateStmts ctx env tail fuel (elseSS ++ rest)
      return guarded cond (.ite cond whenTrue whenFalse)
    else
      let names := changedNames (thenSS ++ elseSS) env
      if names.isEmpty then reject sp "an if that does not return must change a local"
      let whenTrue ← translateStmts ctx env (.state names) fuel thenSS
      let whenFalse ← translateStmts ctx env (.state names) fuel elseSS
      return guarded cond
        (.letState names (.ite cond whenTrue whenFalse) (← translateStmts ctx env tail fuel rest))

end

/-! ### Functions -/

def valueCode : Eval.Val → IR.Expr
  | .int n => .int n
  | .bool b => .bool b
  | .str s => .string s

/-- The first proved counted form starts the function body. Its body uses the
existing state translation, so returns and nested loops remain refused. -/
def translateTop (ctx : Ctx) (env : Env) (result : Ty) (monadic : Bool) : List Stmt → TM IR.Body
  | .forStmt sp init cond post (.block bsp ss) :: rest => do
    let some (index, items) := Eval.countedHead init cond post
      | reject sp "a counted loop needs literal bounds, ++, and at most 256 iterations"
    unless Eval.countedBodySafe index (.block bsp ss) do
      reject sp "the counted body must not change its counter or contain another loop"
    let inner ← declare env sp index .int
    let changed := (env.filter fun l => (changesList ss).contains l.name)
    let body ← translateStmts ctx inner (.state (changed.map (·.name))) stmtFuel ss
    let next ← translateStmts ctx env (.ret result monadic) stmtFuel rest
    return tolean.Core.Loop.lowerLoop sp (changed.map fun l => (l.name, l.type.lean))
      index .int body (.list (items.map valueCode) .int) next false none
  | ss => translateStmts ctx env (.ret result monadic) stmtFuel ss

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
    let b ← translateTop ctx env result false body
    if !b.throws then
      return (.function name (ps.map fun (n, t) => (n, t.lean)) result.lean b,
        ⟨name, ps.map (·.2), result, false⟩)
    -- The function can panic, so it returns an `Except` and `pure` of its
    -- value. The output writes `throw`, which a declaration of the package
    -- would hide.
    if ctx.program.names.contains "throw" then reject sp "the package declares 'throw'"
    let b ← translateTop ctx env result true body
    return (.function name (ps.map fun (n, t) => (n, t.lean)) (.except .string result.lean) b,
      ⟨name, ps.map (·.2), result, true⟩)
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
