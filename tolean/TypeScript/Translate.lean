import tolean.Sexp
import tolean.Version
import tolean.TypeScript.Edition
import tolean.TypeScript.Syntax.Parser
import tolean.TypeScript.Output
import tolean.TypeScript.Spec.Eval

/-!
Translate one TypeScript module, in Tolean's subset, to Lean 4 definitions that
compute the same values.

The translation is a shallow embedding: each function becomes a `def`, each
interface a `structure`, and local mutation becomes shadowed `let`s. A
`for…of` loop becomes `List.foldl` over the tuple of locals it changes. That is
sound only because the subset rules out aliasing: the only mutable values are
locals the function owns (`let` scalars, and `const` arrays that start as
`[]`), and nothing else can observe them.

`number` is never Lean's `Float`. Definitions become generic over an abstract
number type `N` (`tolean.TypeScript.JSNumber`), and `T | null` becomes
`Option T`, with TypeScript's null narrowing as a `match`.

There is no `tsc` here, so the translator types the subset itself: every
expression gets the type that `tsc` gives it, with the same narrowing on
`null`. Where it cannot tell, it refuses. It refuses everything outside the
subset with a position and a reason; nothing is approximated.

The translator does not write text. It builds the output as a syntax tree
(`Output.lean`), and the printer there writes it. So the translator is a
function from one syntax tree to another, which a theorem can be about.
-/
namespace tolean.TypeScript.Translate

open tolean tolean.TypeScript.Syntax

/-- A type of the subset, after narrowing. -/
inductive Ty where
  | bigint | number | boolean | string | null
  /-- `T | null`, where `T` is not `null` and not nullable. -/
  | nullable (value : Ty)
  | array (elem : Ty)
  | struct (name : String)
deriving BEq, Repr, Inhabited

/-- A value of type `source` can stand where `target` is expected. Arrays and
structures must match exactly. -/
def Ty.assignableTo (source target : Ty) : Bool :=
  source == target ||
    match target with
    | .nullable value => source == .null || source == value
    | _ => false

/-- The type of `c ? a : b`. -/
def Ty.join (a b : Ty) : Option Ty :=
  if a == b then some a
  else match a, b with
    | .null, .nullable t | .nullable t, .null => some (.nullable t)
    | .nullable t, u | u, .nullable t => if t == u then some (.nullable t) else none
    | .null, t | t, .null => some (.nullable t)
    | _, _ => none

/-- An object, which `===` compares by identity. -/
def Ty.isObject : Ty → Bool
  | .array _ | .struct _ => true
  | _ => false

/-- The Lean type that the output gives a value of type `t`. -/
def Ty.lean : Ty → Output.Ty
  | .bigint => .int
  | .number => .number
  | .boolean => .bool
  | .string => .string
  | .null => .null
  | .nullable t => .option t.lean
  | .array t => .list t.lean
  | .struct name => .struct name

/-- How a name in scope may be used. Only `let` and `array` locals change. -/
inductive Binding where
  | param | const | «let» | array
deriving BEq, Repr, Inhabited

structure Local where
  name : String
  binding : Binding
  type : Ty

/-- The names in scope, in the order they were declared. -/
structure Env where
  locals : List Local := []

def Env.lookup (env : Env) (name : String) : Option Local := env.locals.find? (·.name == name)

def Env.has (env : Env) (name : String) : Bool := (env.lookup name).isSome

def Env.add (env : Env) (l : Local) : Env := { locals := env.locals ++ [l] }

/-- `name` has the type `type` from here on, as after `x !== null`. -/
def Env.narrow (env : Env) (name : String) (type : Ty) : Env :=
  { locals := env.locals.map fun l => if l.name == name then { l with type } else l }

structure StructInfo where
  name : String
  fields : List (String × Ty)

structure FnInfo where
  name : String
  params : List Ty
  ret : Ty

structure Ctx where
  file : String
  /-- The edition the code runs on. A feature newer than it is refused. -/
  target : Edition
  src : Array Char
  lineStarts : Array Nat
  structs : List StructInfo := []
  functions : List FnInfo := []
  currentFunction : String := ""
  returnType : Ty := .boolean
  /-- A bound on how deep the translator's calls nest. Each nesting of the
  program takes at most a few calls, so four per character of the source is
  more than enough, and running out is a refusal. With the bound, every
  function of the translator is total. -/
  fuel : Nat := 0
  /-- True while translating a `return` value. An owned array may be read
  only there: a later push would shadow the array in Lean but change it in
  JS, so an earlier read (an alias, a field, a loop over it) could see a
  stale value. -/
  returning : Bool := false

abbrev TM := EStateM String Ctx

/-- A translated expression. `prop` is true when the code is a Lean `Prop`,
not a `Bool`. -/
structure Code where
  code : Output.Expr
  prop : Bool
  type : Ty

/-- In value position, a `Prop` becomes a `Bool` with `decide`. -/
def Code.value (c : Code) : Output.Expr :=
  if c.prop then .decide c.code else c.code

/-- What a statement list ends in: a `return`, or the tuple of changed locals. -/
inductive Tail where
  | ret
  | state (names : List String)

def leanReserved : List String :=
  ["_root_", "abbrev", "at", "axiom", "by", "class", "def",
   "deriving", "do", "else", "end", "example", "extends", "for", "from", "fun", "have", "if",
   "import", "in", "inductive", "instance", "let", "match", "mut", "namespace", "open",
   "private", "protected", "return", "section", "show", "structure", "then", "theorem",
   "universe", "unless", "variable", "where", "with", "Type", "Prop", "Sort"]

/-! ### Literal values

The translator reads a literal with the interpreter's own functions,
`Eval.bigintLiteral` and `Eval.numberLiteral`, so the two cannot disagree on
its value. -/

/-- The value of a bigint literal, such as `0xffn`. -/
def bigintValue? (text : String) : Option Nat := (Eval.bigintLiteral text).map Int.toNat

/-- The safe integer that a number literal denotes exactly, or none. A literal
such as `0.5`, or one above `2^53 - 1`, has none. -/
def safeIntegerValue? (text : String) : Option Nat := (Eval.numberLiteral text).map Int.toNat

/-! ### Errors -/

/-- The source text of `span`, at most 80 characters. -/
def spanText (ctx : Ctx) (span : Span) : String :=
  let index (p : Pos) : Nat := (ctx.lineStarts[p.line - 1]?.getD 0) + p.col - 1
  let first := index span.start
  let last := min (index span.stop) (first + 80)
  (ctx.src.extract first last).foldl String.push ""

def reject {A : Type} (span : Span) (reason : String) : TM A := do
  let ctx ← get
  throw s!"{ctx.file}:{span.start.line}:{span.start.col}: {reason}: {spanText ctx span}"

/-- The program nests deeper than `Ctx.fuel` allows. -/
def tooDeep {A : Type} : TM A := do
  throw s!"{(← get).file}: the program is nested too deeply for the translator"

/-- `Ctx.fuel`, for a call into the translator from outside it. -/
def fuelLimit : TM Nat := do return (← get).fuel

/-- Refuse the node at `span` unless the target edition has `f`. -/
def requireFeature (span : Span) (f : Feature) : TM Unit := do
  let target := (← get).target
  unless target.supports f do reject span (f.refusal target)

def checkName (span : Span) (name : String) : TM String := do
  if leanReserved.contains name then reject span s!"name '{name}' is reserved in Lean"
  return name

def declare (env : Env) (span : Span) (name : String) (binding : Binding) (type : Ty) :
    TM Env := do
  if env.has name then reject span s!"'{name}' shadows a name already in scope"
  let _ ← checkName span name
  return env.add { name, binding, type }

/-! ### Types -/

def unsupportedType {A : Type} (t : TypeExpr) : TM A :=
  reject t.span
    ("unsupported type (use bigint, number, boolean, string, T | null, arrays, " ++
      "or an interface declared above)")

/-- The type of `t` in the subset. The output writes it as `Ty.lean`. -/
def translateType (t : TypeExpr) : TM Ty := do
  match t with
  | .keyword s "bigint" =>
    requireFeature s .bigint
    return .bigint
  | .keyword _ "boolean" => return .boolean
  | .keyword _ "string" => return .string
  | .keyword _ "number" => return .number
  | .union _ [a, b] =>
    -- `T | null`: exactly two members, one of them `null`.
    match a, b with
    | .null _, .null _ => unsupportedType t
    | .null _, value | value, .null _ => return .nullable (← translateType value)
    | _, _ => unsupportedType t
  | .array _ elem => return .array (← translateType elem)
  | .ref _ name [elem] =>
    unless name == "Array" || name == "ReadonlyArray" do unsupportedType t
    return .array (← translateType elem)
  | .ref _ name [] =>
    unless (← get).structs.any (·.name == name) do unsupportedType t
    return .struct name
  | _ => unsupportedType t

/-! ### What statements do -/

def blockStatements : Stmt → List Stmt
  | .block _ body => body
  | s => [s]

mutual

/-- Every path through `statements` ends in a `return`. -/
def alwaysReturns : List Stmt → Bool
  | [] => false
  | [s] => endsInReturn s
  | _ :: rest => alwaysReturns rest

/-- `s`, the last statement of a list, ends every path in a `return`. -/
def endsInReturn : Stmt → Bool
  | .returnStmt .. => true
  | .ifStmt _ _ thenBranch (some elseBranch) => branchReturns thenBranch && branchReturns elseBranch
  | _ => false

/-- `alwaysReturns (blockStatements s)`. -/
def branchReturns : Stmt → Bool
  | .block _ body => alwaysReturns body
  | s => endsInReturn s

end

mutual

/-- `s` contains a `return`, `break` or `continue`. -/
def containsJump : Stmt → Bool
  | .returnStmt .. | .breakStmt _ | .continueStmt _ => true
  | .ifStmt _ _ t (some e) => containsJump t || containsJump e
  | .ifStmt _ _ t none => containsJump t
  | .forOfStmt _ _ _ _ body | .whileStmt _ _ body => containsJump body
  | .block _ body => anyContainsJump body
  | _ => false

def anyContainsJump : List Stmt → Bool
  | [] => false
  | s :: rest => containsJump s || anyContainsJump rest

end

mutual

/-- The names that `e` assigns, increments or pushes to. -/
def exprChanges : Expr → List String
  | .assign _ op target value =>
    let own := match target with
      | .ident _ name => if op matches .assign | .add | .sub | .mul then [name] else []
      | _ => []
    own ++ exprChanges target ++ exprChanges value
  | .prefix _ _ (.ident _ name) | .postfix _ _ (.ident _ name) => [name]
  | .prefix _ _ e | .postfix _ _ e | .paren _ e | .unary _ _ e | .member _ e _ => exprChanges e
  | .call _ callee args =>
    let own := match callee with
      | .member _ (.ident _ name) "push" => [name]
      | _ => []
    own ++ exprChanges callee ++ exprsChanges args
  | .array _ elems => exprsChanges elems
  | .object _ props => propsChanges props
  | .index _ a b | .binary _ _ a b => exprChanges a ++ exprChanges b
  | .cond _ a b c => exprChanges a ++ exprChanges b ++ exprChanges c
  | _ => []

def exprsChanges : List Expr → List String
  | [] => []
  | e :: es => exprChanges e ++ exprsChanges es

def propsChanges : List Property → List String
  | [] => []
  | .keyValue _ _ v :: ps => exprChanges v ++ propsChanges ps
  | .shorthand .. :: ps => propsChanges ps

end

def optionChanges : Option Expr → List String
  | some e => exprChanges e
  | none => []

mutual

def stmtChanges : Stmt → List String
  | .varDecl _ d => optionChanges d.init
  | .exprStmt _ e => exprChanges e
  | .returnStmt _ v => optionChanges v
  | .ifStmt _ test t (some e) => exprChanges test ++ stmtChanges t ++ stmtChanges e
  | .ifStmt _ test t none => exprChanges test ++ stmtChanges t
  | .forOfStmt _ _ _ iterable body => exprChanges iterable ++ stmtChanges body
  | .whileStmt _ test body => exprChanges test ++ stmtChanges body
  | .block _ body => stmtsChanges body
  | _ => []

def stmtsChanges : List Stmt → List String
  | [] => []
  | s :: rest => stmtChanges s ++ stmtsChanges rest

end

/-- The locals of `env` that `statements` change, in the order of `env`. -/
def changedNames (statements : List Stmt) (env : Env) : List String :=
  let changed := stmtsChanges statements
  (env.locals.filter fun l => changed.contains l.name).map (·.name)

/-- `x === null` or `x !== null`, where `x` is a name in scope that may be
`null` here: `(x, the test is ===, the type of x when not null)`. A name
already narrowed is not an `Option` in Lean any more, so it gets no `match`. -/
def nullTestOf (env : Env) (e : Expr) : Option (String × Bool × Ty) :=
  match e.stripParens with
  | .binary _ op l r =>
    if !(op == .strictEq || op == .strictNe) then none
    else
      let other? := if r matches .null _ then some l else if l matches .null _ then some r else none
      match other? with
      | some (.ident _ name) =>
        match env.lookup name with
        | some { type := .nullable value, .. } => some (name, op == .strictEq, value)
        | _ => none
      | _ => none
  | _ => none

/-- A bigint literal other than `0n`, such as `2n` or `-(3n)`. -/
def isNonzeroBigintLiteral : Expr → Bool
  | .paren _ inner | .unary _ .neg inner => isNonzeroBigintLiteral inner
  | .bigint _ text => (bigintValue? text).any (· != 0)
  | _ => false

def numberTest? : String → Option Output.NumberTest
  | "isSafeInteger" => some .isSafeInteger
  | "isNaN" => some .isNaN
  | "isFinite" => some .isFinite
  | _ => none

def numberConstant? : String → Option Output.NumberConstant
  | "NaN" => some .nan
  | "Infinity" => some .posInf
  | _ => none

/-! ### Expressions -/

mutual

/-- `expected` is the type the context gives, which an object literal needs:
the return type, a declared type, a parameter type or a field type. -/
def translateExpr (fuel : Nat) (env : Env) (expected : Option Ty) (e : Expr) : TM Code := do
  let fuel + 1 := fuel | tooDeep
  match e with
  | .paren _ inner => translateExpr fuel env expected inner
  | .bigint _ text =>
    -- Typed, so Lean never defaults a numeral to `Nat`, where `0 - 1 = 0`.
    let some v := bigintValue? text | reject e.span "a bigint literal must be an integer"
    return ⟨.int v, false, .bigint⟩
  | .number s text =>
    let some v := safeIntegerValue? text | reject s "a number literal must be a safe integer"
    return ⟨.number v, false, .number⟩
  | .null _ => return ⟨.none, false, .null⟩
  | .bool _ value => return ⟨.bool value, false, .boolean⟩
  | .string _ value => return ⟨.string value, false, .string⟩
  | .ident s name =>
    match env.lookup name with
    | none =>
      let some constant := numberConstant? name
        | reject s "only parameters and locals may be referenced"
      return ⟨.numberConstant constant, false, .number⟩
    | some l =>
      if l.binding == .array && !(← get).returning then
        reject s "an owned array may be read only in the return value"
      return ⟨.var name, false, l.type⟩
  | .member s obj name =>
    let o ← translateExpr fuel env none obj
    let ctx : Ctx ← get
    let field? := match o.type with
      | .struct structName =>
        (ctx.structs.find? fun (i : StructInfo) => i.name == structName).bind
          fun info => info.fields.lookup name
      | _ => none
    let some type := field? | reject s "only fields of interfaces declared in this file may be read"
    return ⟨.field o.code (!(obj matches .ident ..)) name, false, type⟩
  | .unary s op arg =>
    if op == .neg && (arg matches .ident _ "Infinity") && !env.has "Infinity" then
      return ⟨.numberConstant .negInf, false, .number⟩
    let a ← translateExpr fuel env none arg
    match op with
    | .not =>
      unless a.type == .boolean do reject s "'!' needs a boolean"
      return if a.prop then ⟨.propNot a.code, true, .boolean⟩
        else ⟨.not a.code, false, .boolean⟩
    | .neg =>
      match a.type with
      | .bigint => return ⟨.neg a.value, false, .bigint⟩
      | .number => return ⟨.numberNeg a.value, false, .number⟩
      | _ => reject s "unsupported unary operator"
    | _ => reject s "unsupported unary operator"
  | .binary s op l r => translateBinary fuel env s op l r
  | .cond s test ifTrue ifFalse =>
    let c ← translateExpr fuel env none test
    unless c.type == .boolean do reject test.span "a condition must be a boolean"
    let a ← translateExpr fuel env expected ifTrue
    let b ← translateExpr fuel env expected ifFalse
    let some type := a.type.join b.type | reject s "the branches of '?:' have different types"
    return ⟨.ite c.code a.value b.value, false, type⟩
  | .call s callee args => translateCall fuel env s callee args
  | .object s props => translateObject fuel env expected s props
  | .array s elems => translateArray fuel env expected s elems
  | _ => reject e.span "unsupported expression"

/-- An array literal, as a list. In JS a literal makes a new array, and only
an owned array may be pushed to, so nothing changes the array after it is
made, and a Lean list has its meaning. The element type comes from the
context, or else from the elements. -/
def translateArray (fuel : Nat) (env : Env) (expected : Option Ty) (s : Span) (elems : List Expr) :
    TM Code := do
  let fuel + 1 := fuel | tooDeep
  let (values, elem) ← translateElements fuel env expected s elems
  return ⟨.list values elem.lean, false, .array elem⟩

/-- The elements of an array literal, and their type. -/
def translateElements (fuel : Nat) (env : Env) (expected : Option Ty) (s : Span) (elems : List Expr) :
    TM (List Output.Expr × Ty) := do
  let fuel + 1 := fuel | tooDeep
  let expectedElem := match expected with
    | some (.array t) => some t
    | _ => none
  let codes ← elems.mapM (translateExpr fuel env expectedElem)
  let elem ← match expectedElem with
    | some t => pure t
    | none =>
      let some first := codes.head?
        | reject s "an empty array needs a declared type, such as 'const xs: ReadonlyArray<bigint> = []'"
      let some t := codes.foldl (fun acc c => acc.bind (·.join c.type)) (some first.type)
        | reject s "the elements of an array must have one type"
      pure t
  for (c, e) in codes.zip elems do
    unless c.type.assignableTo elem do reject e.span "the element does not have the array's element type"
  return (codes.map (·.value), elem)

def translateCall (fuel : Nat) (env : Env) (s : Span) (callee : Expr) (args : List Expr) : TM Code := do
  let fuel + 1 := fuel | tooDeep
  -- `Number.isNaN(x)` and the like. TypeScript lets them take any value; the
  -- model has them on numbers only.
  if let .member _ (.ident _ "Number") test := callee then
    if let (false, some form, [arg]) := (env.has "Number", numberTest? test, args) then
      let a ← translateExpr fuel env none arg
      unless a.type == .number do
        reject arg.span s!"Number.{test} needs a number operand (narrow a nullable value first)"
      return ⟨.numberTest form a.value, false, .boolean⟩
  let noCall {A : Type} : TM A :=
    reject s "calls may name only functions declared earlier in this file (no recursion)"
  let .ident _ name := callee | noCall
  let ctx ← get
  if (name == "isNaN" || name == "isFinite") && !ctx.functions.any (·.name == name) then
    reject s s!"the global {name} converts its argument to a number; use Number.{name}"
  let some fn := ctx.functions.find? (·.name == name) | noCall
  if env.has name then noCall
  unless fn.params.length == args.length do reject s s!"'{name}' takes {fn.params.length} arguments"
  let mut values := #[]
  for (arg, paramType) in args.zip fn.params do
    let a ← translateExpr fuel env (some paramType) arg
    unless a.type.assignableTo paramType do
      reject arg.span "the argument does not have the parameter's type"
    values := values.push a.value
  return ⟨.call name values.toList, false, fn.ret⟩

def translateObject (fuel : Nat) (env : Env) (expected : Option Ty) (s : Span) (props : List Property) :
    TM Code := do
  let fuel + 1 := fuel | tooDeep
  let ctx ← get
  let notStruct {A : Type} : TM A :=
    reject s "an object literal must build an interface declared in this file"
  let some (.struct structName) := expected | notStruct
  let some info := ctx.structs.find? (·.name == structName) | notStruct
  let mut seen : List String := []
  let mut parts := #[]
  for p in props do
    let (key, value, span) ← match p with
      | .shorthand ps name => pure (name, Expr.ident ps name, ps)
      | .keyValue ps (.ident key) v => pure (key, v, ps)
      | .keyValue ps _ _ => reject ps "object literal fields must be plain name: value pairs"
    let some fieldType := info.fields.lookup key
      | reject span s!"'{key}' is not a field of {structName}"
    if seen.contains key then reject span s!"'{key}' is set twice"
    seen := seen ++ [key]
    let v ← translateExpr fuel env (some fieldType) value
    unless v.type.assignableTo fieldType do reject span s!"'{key}' does not have the field's type"
    parts := parts.push (key, v.value)
  for (field, _) in info.fields do
    unless seen.contains field do reject s s!"the object lacks the field '{field}'"
  -- A JS object keeps its keys in the order the literal writes them, and the
  -- caller can see that order, through `Object.keys` or `JSON.stringify`. A
  -- Lean structure has no order, so the literal must use the declared one.
  let declared := info.fields.map (·.1)
  unless seen == declared do
    reject s s!"write the fields in the order that {structName} declares them: {", ".intercalate declared}"
  return ⟨.struct parts.toList structName, false, .struct structName⟩

def translateBinary (fuel : Nat) (env : Env) (s : Span) (op : BinOp) (l r : Expr) : TM Code := do
  let fuel + 1 := fuel | tooDeep
  -- `x === null` and `x !== null`: a test on a Lean `Option`.
  if (op == .strictEq || op == .strictNe) && ((l matches .null _) || (r matches .null _)) then
    let other := if l matches .null _ then r else l
    if other matches .null _ then reject s "compare null with a value, not with null"
    let isEquality := op == .strictEq
    let o ← translateExpr fuel env none other
    match o.type with
    | .nullable _ =>
      return ⟨if isEquality then .isNone o.code else .isSome o.code, false, .boolean⟩
    | _ =>
      -- The type fixes the answer, as after `if (x === null) return …`. The
      -- test then does nothing, and a constant answer would drop the operand,
      -- which the interpreter still evaluates. So the subset refuses it.
      reject s "the type fixes the answer of this test with null, so it does nothing; remove it"
  -- `x === null || e` and `x !== null && e`: TypeScript narrows `x` in `e`,
  -- so Lean matches on `x` and binds it to the value inside.
  if let some (name, isNullTest, value) := nullTestOf env l then
    if (op == .or && isNullTest) || (op == .and && !isNullTest) then
      let whenSome ← translateExpr fuel (env.narrow name value) none r
      unless whenSome.type == .boolean do reject r.span s!"'{op.symbol}' needs two booleans"
      return ⟨.matchNull name (.bool (op == .or)) whenSome.value, false, .boolean⟩
  let a ← translateExpr fuel env none l
  let b ← translateExpr fuel env none r
  let bothBigInt := a.type == .bigint && b.type == .bigint
  let bothNumber := a.type == .number && b.type == .number
  let call (op : Output.NumberOp) (x y : Code) (type : Ty) : Code :=
    ⟨.numberOp op x.value y.value, false, type⟩
  let arithmetic (bigintOp : Output.IntOp) (numberOp : Output.NumberOp) : TM Code := do
    if bothNumber then return call numberOp a b .number
    unless bothBigInt do reject s "arithmetic needs two bigints or two numbers"
    return ⟨.intOp bigintOp a.value b.value, false, .bigint⟩
  -- `a > b` is `b < a`, and `a >= b` is `b <= a`.
  let compare (bigintOp : Output.Order) (numberOp : Output.NumberOp) (swap : Bool) : TM Code := do
    if bothNumber then
      return if swap then call numberOp b a .boolean else call numberOp a b .boolean
    unless bothBigInt do reject s "ordering needs two bigints or two numbers"
    return ⟨.order bigintOp a.value b.value, true, .boolean⟩
  let equal (negated : Bool) : TM Code := do
    if bothNumber then
      return if negated then ⟨.numberNe a.value b.value, false, .boolean⟩
        else call .eq a b .boolean
    if a.type.isObject || b.type.isObject || (a.type matches .nullable _) ||
        (b.type matches .nullable _) then
      reject s ("=== here would compare objects or nullable values; " ++
        "only primitives and null tests are supported")
    unless a.type == b.type && (a.type matches .boolean | .string | .bigint) do
      reject s "=== needs two values of the same primitive type"
    return ⟨if negated then .ne a.value b.value else .eq a.value b.value, true, .boolean⟩
  -- bigint `/` truncates toward zero and `%` takes the sign of the dividend:
  -- Lean's `Int.tdiv` and `Int.tmod`. JS throws on a zero divisor, where Lean
  -- gives a value, so the divisor must be a nonzero literal.
  let divide (operation : Output.Division) : TM Code := do
    unless bothBigInt && isNonzeroBigintLiteral r do
      reject s "'/' and '%' need two bigints and a nonzero bigint literal divisor (JS throws on 0n)"
    requireFeature s .bigintDivision
    return ⟨.division operation a.value b.value, false, .bigint⟩
  let logical (isAnd : Bool) : TM Code := do
    unless a.type == .boolean && b.type == .boolean do
      reject s s!"'{op.symbol}' needs two booleans"
    if a.prop && b.prop then
      return ⟨if isAnd then .propAnd a.code b.code else .propOr a.code b.code, true, .boolean⟩
    return ⟨if isAnd then .and a.value b.value else .or a.value b.value, false, .boolean⟩
  match op with
  | .add => arithmetic .add .add
  | .sub => arithmetic .sub .sub
  | .mul => arithmetic .mul .mul
  | .div => divide .tdiv
  | .mod => divide .tmod
  | .lt => compare .lt .lt false
  | .le => compare .le .le false
  | .gt => compare .gt .lt true
  | .ge => compare .ge .le true
  | .strictEq => equal false
  | .strictNe => equal true
  | .and => logical true
  | .or => logical false
  | _ => reject s "unsupported binary operator"

end

/-! ### Statements -/

def assignOps? : AssignOp → Option (Output.IntOp × Output.NumberOp)
  | .add => some (.add, .add)
  | .sub => some (.sub, .sub)
  | .mul => some (.mul, .mul)
  | _ => none

/-- One mutation statement, as the local it changes and its new value. -/
def translateUpdate (env : Env) (s : Span) (e : Expr) : TM (String × Output.Expr) := do
  let refuse {A : Type} : TM A :=
    reject s "an expression statement must assign a let local or push to an owned array"
  match e with
  | .call _ (.member _ (.ident _ target) "push") args =>
    let refusePush {A : Type} : TM A :=
      reject s "push is allowed only onto an owned array, one element at a time"
    let some { binding := .array, type := .array elemType, .. } := env.lookup target | refusePush
    let [element] := args | refusePush
    let v ← translateExpr (← fuelLimit) env (some elemType) element
    unless v.type.assignableTo elemType do
      reject element.span "the element does not have the array's element type"
    return (target, .push target v.value)
  | .assign _ op (.ident _ name) right =>
    unless op matches .assign | .add | .sub | .mul do refuse
    let some { binding := .«let», type, .. } := env.lookup name
      | reject s "only a local declared with let may be assigned"
    let v ← translateExpr (← fuelLimit) env (some type) right
    match assignOps? op with
    | none =>
      unless v.type.assignableTo type do reject s "the value does not have the local's type"
      return (name, v.value)
    | some (bigintOp, numberOp) =>
      -- On `number` the operation goes through the abstract number model.
      if type == .number && v.type == .number then
        return (name, .numberOp numberOp (.var name) v.value)
      unless type == .bigint && v.type == .bigint do
        reject s "arithmetic needs two bigints or two numbers"
      return (name, .update bigintOp name v.value)
  | _ => refuse

mutual

def translateStatements (fuel : Nat) (env : Env) (tail : Tail) (statements : List Stmt) :
    TM Output.Body := do
  let fuel + 1 := fuel | tooDeep
  match statements with
  | [] =>
    match tail with
    | .ret =>
      let ctx ← get
      throw s!"{ctx.file}: '{ctx.currentFunction}' can end without a return"
    | .state names => return .state names
  | stmt :: rest =>
    match stmt with
    | .returnStmt s value =>
      let (.ret, [], some v) := (tail, rest, value)
        | reject s "return must be the last statement of a function and carry a value"
      modify fun c => { c with returning := true }
      let returnType := (← get).returnType
      let code ← translateExpr (← fuelLimit) env (some returnType) v
      unless code.type.assignableTo returnType do
        reject v.span "the value does not have the function's return type"
      modify fun c => { c with returning := false }
      return .value code.value
    | .varDecl s d => translateVariable fuel env s d rest tail
    | .exprStmt s e =>
      let (name, update) ← translateUpdate env s e
      return .let name update (← translateStatements fuel env tail rest)
    | .ifStmt s test thenBranch elseBranch =>
      translateIf fuel env s test thenBranch elseBranch rest tail
    | .forOfStmt s kind name iterable body =>
      translateForOf fuel env s kind name iterable body rest tail
    | _ => reject stmt.span "unsupported statement"

def translateVariable (fuel : Nat) (env : Env) (s : Span) (d : VarDecl) (rest : List Stmt)
    (tail : Tail) : TM Output.Body := do
  let fuel + 1 := fuel | tooDeep
  let some init := d.init | reject s "declare one const or let identifier with an initializer"
  -- `const xs: Array<T> = [...]` (or `T[]`) is an owned array, which the
  -- function may push to. Any other array literal is a value.
  let mutableAnnotation := match d.type with
    | some (.ref _ "Array" [_]) | some (.array _ _) => true
    | _ => false
  if init matches .array .. then
    if mutableAnnotation then
      unless d.kind == .const do
        reject s "an array that the function pushes to must be 'const xs: Array<T> = [...]'; use ReadonlyArray<T> for a value"
      let some annotation := d.type | unreachable!
      let type ← translateType annotation
      let .array _ elems := init | unreachable!
      -- The `let` states the type, so the list needs no ascription.
      let (values, _) ← translateElements (← fuelLimit) env (some type) s elems
      let env' ← declare env s d.name .array type
      return .letArray d.name type.lean values (← translateStatements fuel env' tail rest)
  let declared ← match d.type with
    | some annotation => some <$> translateType annotation
    | none => pure none
  let code ← translateExpr (← fuelLimit) env declared init
  let type ← match declared with
    | some t =>
      if code.type.assignableTo t then pure t
      else reject s "the value does not have the declared type"
    | none => pure code.type
  let binding := if d.kind == .const then Binding.const else .«let»
  let env' ← declare env s d.name binding type
  return .let d.name code.value (← translateStatements fuel env' tail rest)

def translateIf (fuel : Nat) (env : Env) (s : Span) (test : Expr) (thenBranch : Stmt)
    (elseBranch : Option Stmt) (rest : List Stmt) (tail : Tail) : TM Output.Body := do
  let fuel + 1 := fuel | tooDeep
  let thenStatements := blockStatements thenBranch
  let elseStatements := (elseBranch.map blockStatements).getD []
  -- `if (x === null)` and `if (x !== null)`: TypeScript narrows `x` in each
  -- branch, so Lean matches on `x` and binds it to the value.
  let nullTest := nullTestOf env test
  let (envTrue, envFalse) := match nullTest with
    | some (name, true, value) => (env.narrow name .null, env.narrow name value)
    | some (name, false, value) => (env.narrow name value, env.narrow name .null)
    | none => (env, env)
  let branch (whenTrue whenFalse : Output.Body) : TM Output.Body := do
    match nullTest with
    | none =>
      let c ← translateExpr (← fuelLimit) env none test
      unless c.type == .boolean do reject test.span "a condition must be a boolean"
      return .ite c.code whenTrue whenFalse
    | some (name, isNullTest, _) =>
      return if isNullTest then .matchNull name whenTrue whenFalse
        else .matchNull name whenFalse whenTrue
  if (tail matches .ret) && alwaysReturns thenStatements then
    if elseBranch.isSome && !rest.isEmpty then
      reject s "code after an if whose branches both return is unreachable"
    let whenTrue ← translateStatements fuel envTrue tail thenStatements
    let whenFalse ← translateStatements fuel envFalse tail (elseStatements ++ rest)
    return (← branch whenTrue whenFalse)
  if (thenStatements ++ elseStatements).any containsJump then
    reject s "a branch that does not always return may not return, break or continue"
  let names := changedNames (thenStatements ++ elseStatements) env
  if names.isEmpty then reject s "an if without a return must change a local"
  if let some (name, _, _) := nullTest then
    if names.contains name then
      reject s "a local tested against null may not be assigned in that if"
  let state := Tail.state names
  let whenTrue ← translateStatements fuel envTrue state thenStatements
  let whenFalse ← translateStatements fuel envFalse state elseStatements
  return .letState names (← branch whenTrue whenFalse) (← translateStatements fuel env tail rest)

def translateForOf (fuel : Nat) (env : Env) (s : Span) (kind : VarKind) (element : String)
    (iterable : Expr) (body : Stmt) (rest : List Stmt) (tail : Tail) : TM Output.Body := do
  let fuel + 1 := fuel | tooDeep
  unless kind == .const do reject s "a loop must be 'for (const x of xs)'"
  let bodyStatements := blockStatements body
  if bodyStatements.any containsJump then reject s "a loop body may not return, break or continue"
  let names := changedNames bodyStatements env
  if names.isEmpty then reject s "a loop must change a local"
  let items ← translateExpr (← fuelLimit) env none iterable
  let .array elemType := items.type | reject iterable.span "a loop must run over an array"
  let bodyEnv ← declare env s element .const elemType
  let bodyOut ← translateStatements fuel bodyEnv (.state names) bodyStatements
  let info : Output.LoopInfo :=
    { span := s, elem := elemType.lean,
      stateTypes := names.filterMap fun n => (env.lookup n).map (·.type.lean),
      scope := (env.locals.filter fun l => !names.contains l.name).map fun l => (l.name, l.type.lean) }
  return .fold names element bodyOut items.code (← translateStatements fuel env tail rest) info

end

/-! ### Declarations -/

def declareTopLevel (s : Span) (name : String) : TM Unit := do
  let ctx ← get
  if ctx.structs.any (·.name == name) || ctx.functions.any (·.name == name) then
    reject s s!"'{name}' is declared twice"

def translateInterface (s : Span) (name : String) (fields : List Field) : TM Output.Decl := do
  let name ← checkName s name
  declareTopLevel s name
  let mut infos := #[]
  for f in fields do
    unless f.readonly && !f.optional do
      reject f.span "interface fields must be readonly, required and typed"
    let field ← checkName f.span f.name
    if infos.any (·.1 == field) then reject f.span s!"'{field}' is declared twice"
    infos := infos.push (field, ← translateType f.type)
  modify fun c => { c with structs := c.structs ++ [{ name, fields := infos.toList }] }
  return .struct name (infos.toList.map fun (field, type) => (field, type.lean))

def translateFunction (s : Span) (name : String) (params : List Param)
    (returnType : Option TypeExpr) (body : Stmt) : TM Output.Decl := do
  let some returnType := returnType
    | reject s "functions must be named, typed, non-generic and synchronous"
  let name ← checkName s name
  declareTopLevel s name
  let mut env : Env := {}
  let mut leanParams := #[]
  let mut types := #[]
  for p in params do
    let some type := p.type | reject p.span "parameters must be plain, typed identifiers"
    let paramName ← checkName p.span p.name
    if env.has paramName then reject p.span s!"'{paramName}' is declared twice"
    let ty ← translateType type
    env := env.add { name := paramName, binding := .param, type := ty }
    leanParams := leanParams.push (paramName, ty.lean)
    types := types.push ty
  let ret ← translateType returnType
  modify fun c => { c with currentFunction := name, returnType := ret }
  let out ← translateStatements (← fuelLimit) env .ret (blockStatements body)
  modify fun c => { c with functions := c.functions ++ [{ name, params := types.toList, ret }] }
  return .function name leanParams.toList ret.lean out

/-! ### The number model -/

def isNumberName (name : String) : Bool :=
  name == "Number" || name == "NaN" || name == "Infinity"

mutual

def typeUsesNumber : TypeExpr → Bool
  | .keyword _ name => name == "number"
  | .literal _ (.number _) => true
  | .ref _ name args => isNumberName name || typesUseNumber args
  | .array _ e | .paren _ e => typeUsesNumber e
  | .union _ members => typesUseNumber members
  | _ => false

def typesUseNumber : List TypeExpr → Bool
  | [] => false
  | t :: ts => typeUsesNumber t || typesUseNumber ts

end

def keyUsesNumber : PropKey → Bool
  | .ident name => isNumberName name
  | .number _ => true
  | .string _ => false

mutual

def exprUsesNumber : Expr → Bool
  | .ident _ name => isNumberName name
  | .number .. => true
  | .member _ obj name => isNumberName name || exprUsesNumber obj
  | .object _ props => propsUseNumber props
  | .array _ es => exprsUseNumber es
  | .call _ f args => exprUsesNumber f || exprsUseNumber args
  | .paren _ e | .unary _ _ e | .prefix _ _ e | .postfix _ _ e => exprUsesNumber e
  | .index _ a b | .binary _ _ a b | .assign _ _ a b => exprUsesNumber a || exprUsesNumber b
  | .cond _ a b c => exprUsesNumber a || exprUsesNumber b || exprUsesNumber c
  | _ => false

def exprsUseNumber : List Expr → Bool
  | [] => false
  | e :: es => exprUsesNumber e || exprsUseNumber es

def propsUseNumber : List Property → Bool
  | [] => false
  | .shorthand _ name :: ps => isNumberName name || propsUseNumber ps
  | .keyValue _ key value :: ps => (keyUsesNumber key || exprUsesNumber value) || propsUseNumber ps

end

def varUsesNumber (d : VarDecl) : Bool :=
  isNumberName d.name || (d.type.map typeUsesNumber).getD false ||
    (d.init.map exprUsesNumber).getD false

mutual

def stmtUsesNumber : Stmt → Bool
  | .varDecl _ d => varUsesNumber d
  | .exprStmt _ e => exprUsesNumber e
  | .returnStmt _ v => (v.map exprUsesNumber).getD false
  | .ifStmt _ test t (some e) => exprUsesNumber test || stmtUsesNumber t || stmtUsesNumber e
  | .ifStmt _ test t none => exprUsesNumber test || stmtUsesNumber t
  | .forOfStmt _ _ name iterable body =>
    isNumberName name || exprUsesNumber iterable || stmtUsesNumber body
  | .whileStmt _ test body => exprUsesNumber test || stmtUsesNumber body
  | .block _ body => stmtsUseNumber body
  | _ => false

def stmtsUseNumber : List Stmt → Bool
  | [] => false
  | s :: rest => stmtUsesNumber s || stmtsUseNumber rest

end

/-- The file uses the number model: a `number` type, a number literal, or the
name `Number`, `NaN` or `Infinity` anywhere. A file can use
`Number.isNaN(NaN)` with no `number` keyword, and it still needs `N`. -/
def moduleUsesNumber (m : Module) : Bool :=
  m.decls.any fun
    | .function _ _ name params ret body =>
      isNumberName name ||
        params.any (fun p => isNumberName p.name || (p.type.map typeUsesNumber).getD false) ||
        (ret.map typeUsesNumber).getD false || stmtUsesNumber body
    | .interface _ _ name fields =>
      isNumberName name || fields.any fun f => isNumberName f.name || typeUsesNumber f.type
    | .typeAlias _ _ name type => isNumberName name || typeUsesNumber type
    | .exportedVar _ d => varUsesNumber d
    | .stmt st => stmtUsesNumber st

/-! ### The module -/

/-- The declarations of `m`, translated. This is the translator as a function
from one syntax tree to another: `translate` parses the source before it and
prints the result after it. -/
def translateDecls (m : Module) : TM (List Output.Decl) :=
  m.decls.mapM fun
    | .interface s _ name fields => translateInterface s name fields
    | .function s _ name params ret body => translateFunction s name params ret body
    | d => reject d.span "only interfaces and functions may appear at top level"

def lineStarts (src : Array Char) : Array Nat := Id.run do
  let mut starts := #[0]
  let mut i := 0
  while i < src.size do
    let c := src[i]!
    if c == '\r' && src[i + 1]? == some '\n' then
      starts := starts.push (i + 2)
      i := i + 2
    else
      if c == '\n' || c == '\r' || c.toNat == 0x2028 || c.toNat == 0x2029 then
        starts := starts.push (i + 1)
      i := i + 1
  return starts

/-- Parse and translate `source`, the TypeScript file `file`: the parsed
module, the names that the printer needs, and the output tree. -/
def translateTree (file source : String) (target : Edition := .default) :
    Except String (Module × Output.Names × List Output.Decl) := do
  let m ← (parse source target).mapError (·.render file)
  let src := source.toList.toArray
  -- Every identifier in the source, at any level. A Lean name in this list is
  -- written from the root, and the number type parameter avoids it.
  let idents := match Syntax.lex source target with
    | .ok tokens => tokens.toList.filterMap fun (t : Syntax.Token) => match t.kind with
      | .ident name => some name
      | _ => none
    | .error _ => []
  let numberVar := ("N" :: (List.range 1000).map (s!"N{· + 1}")).find? (!idents.contains ·)
  let names : Output.Names :=
    { clashes := Output.leanNames.map (·.1) |>.filter idents.contains,
      numberVar := numberVar.getD "N", usesNumber := moduleUsesNumber m }
  let ctx : Ctx := { file, target, src, lineStarts := lineStarts src, fuel := 4 * src.size + 4 }
  match (translateDecls m).run ctx with
  | .error e _ => .error e
  | .ok decls _ => return (m, names, decls)

/-- Translate `source`, the TypeScript file `file`, to a Lean file whose
definitions are in namespace `ns`, for code that runs on the edition
`target`. -/
def translate (file source ns : String) (target : Edition := .default) :
    Except String String := do
  let (_, names, decls) ← translateTree file source target
  let header :=
    if names.usesNumber then ["import tolean.TypeScript.Spec.Number", "", "open tolean.TypeScript"]
    else []
  return "\n".intercalate
    ([s!"-- Generated by tolean {version} for {target.name} from {file}. Do not edit."] ++
      header ++
      [s!"namespace {ns}", "", "\n\n".intercalate (decls.map (·.print names)), "", s!"end {ns}", ""])

end tolean.TypeScript.Translate
