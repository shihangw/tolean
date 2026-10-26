import tolean.Sexp
import tolean.Version
import tolean.TypeScript.Edition
import tolean.TypeScript.Syntax.Parser

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

On every file that both accept, the output is the same, byte for byte, as the
TypeScript translator in `npm/src/translate.ts`
(`tests/typescript/checkTranslate.ts` checks this).
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
  usesNumber : Bool
  /-- Lean names the output uses that the source also declares. The output
  writes them in full from the root, so a source name never hides them. -/
  clashes : List String := []
  /-- The number type parameter: `N`, or a fresh name when the source uses `N`. -/
  numberVar : String := "N"
  structs : List StructInfo := []
  functions : List FnInfo := []
  currentFunction : String := ""
  returnType : Ty := .boolean
  /-- True while translating a `return` value. An owned array may be read
  only there: a later push would shadow the array in Lean but change it in
  JS, so an earlier read (an alias, a field, a loop over it) could see a
  stale value. -/
  returning : Bool := false

abbrev TM := EStateM String Ctx

/-- A translated expression. `prop` is true when the code is a Lean `Prop`,
not a `Bool`. -/
structure Code where
  code : String
  prop : Bool
  type : Ty

/-- The Lean names the output uses, with their full names from the root. -/
def leanNames : List (String × String) :=
  [("decide", "Decidable.decide"), ("List", "List"), ("Option", "Option"),
   ("some", "Option.some"), ("none", "Option.none"), ("Int", "Int"), ("Bool", "Bool"),
   ("String", "String"), ("JSNumber", "tolean.TypeScript.JSNumber")]

/-- Write the Lean name `name` (or `name.rest`), from the root when the source
declares the same name. -/
def leanName (name : String) : TM String := do
  let (head, rest) := match name.splitOn "." with
    | h :: t => (h, String.join (t.map ("." ++ ·)))
    | [] => (name, "")
  if (← get).clashes.contains head then
    return s!"_root_.{(leanNames.lookup head).getD head}{rest}"
  return name

/-- The number type parameter. -/
def numberVar : TM String := do return (← get).numberVar

/-- In value position, a `Prop` becomes a `Bool` with `decide`. -/
def Code.value (c : Code) : TM String := do
  if c.prop then return s!"{← leanName "decide"} ({c.code})" else return c.code

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

/-! ### Literal values -/

def digitValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def digitsValue (radix : Nat) (digits : List Char) : Nat :=
  digits.foldl (fun acc c => acc * radix + digitValue c) 0

/-- The value of an integer literal with a `0x`, `0o` or `0b` prefix, or none. -/
def prefixedValue? : List Char → Option Nat
  | '0' :: p :: digits =>
    if p == 'x' || p == 'X' then some (digitsValue 16 digits)
    else if p == 'o' || p == 'O' then some (digitsValue 8 digits)
    else if p == 'b' || p == 'B' then some (digitsValue 2 digits)
    else none
  | _ => none

def maxSafeInteger : Nat := 2 ^ 53 - 1

/-- The safe integer that a number literal denotes exactly, or none. A literal
such as `0.5`, or one above `2^53 - 1`, has none. -/
def safeIntegerValue? (text : String) : Option Nat := do
  let chars := text.toList.filter (· != '_')
  let value ← match prefixedValue? chars with
    | some v => some v
    | none =>
      let (mantissa, exponent) := chars.span fun c => c != 'e' && c != 'E'
      let exp : Int ← match exponent with
        | [] => some 0
        | _ :: '-' :: ds => some (-(digitsValue 10 ds : Int))
        | _ :: '+' :: ds | _ :: ds => some (digitsValue 10 ds : Int)
      let (whole, fraction) := mantissa.span (· != '.')
      let fraction := fraction.drop 1
      let m := digitsValue 10 (whole ++ fraction)
      let scale := exp - fraction.length
      if m == 0 then some 0
      else if scale ≥ 0 then
        -- `m ≥ 1`, so anything past 10^16 is above 2^53.
        if scale > 16 then none else some (m * 10 ^ scale.toNat)
      else
        let k := (-scale).toNat
        if k > 400 then none
        else if m % 10 ^ k == 0 then some (m / 10 ^ k) else none
  if value ≤ maxSafeInteger then some value else none

/-- The value of a bigint literal, such as `0xffn`. -/
def bigintValue (text : String) : Nat :=
  let chars := (text.toList.filter (· != '_')).dropLast
  (prefixedValue? chars).getD (digitsValue 10 chars)

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

/-- Lean code as an argument: parenthesized unless it is one atom. A prefix
`!` or `¬` takes the rest of the line in Lean, so code that starts with one is
not an atom even without a space: `f !(a) b` reads as `f !((a) b)`. -/
def argument (code : String) : String :=
  if code.contains ' ' || code.startsWith "!" || code.startsWith "¬" then s!"({code})" else code

def wrapped (constructor argument : String) : String :=
  constructor ++ " " ++
    (if argument.contains ' ' && !argument.startsWith "(" then s!"({argument})" else argument)

def structType (ctx : Ctx) (name : String) : String :=
  if ctx.usesNumber then s!"({name} {ctx.numberVar})" else name

def unsupportedType {A : Type} (t : TypeExpr) : TM A :=
  reject t.span
    ("unsupported type (use bigint, number, boolean, string, T | null, arrays, " ++
      "or an interface declared above)")

/-- The Lean type of `t`, and its type in the subset. -/
partial def translateType (t : TypeExpr) : TM (String × Ty) := do
  match t with
  | .keyword s "bigint" =>
    requireFeature s .bigint
    return (← leanName "Int", .bigint)
  | .keyword _ "boolean" => return (← leanName "Bool", .boolean)
  | .keyword _ "string" => return (← leanName "String", .string)
  | .keyword _ "number" => return (← numberVar, .number)
  | .union _ [a, b] =>
    -- `T | null`: exactly two members, one of them `null`.
    let value? := match a, b with
      | .null _, .null _ => none
      | .null _, v | v, .null _ => some v
      | _, _ => none
    let some value := value? | unsupportedType t
    let (lean, ty) ← translateType value
    return (wrapped (← leanName "Option") lean, .nullable ty)
  | .array _ elem =>
    let (lean, ty) ← translateType elem
    return (wrapped (← leanName "List") lean, .array ty)
  | .ref _ name [elem] =>
    unless name == "Array" || name == "ReadonlyArray" do unsupportedType t
    let (lean, ty) ← translateType elem
    return (wrapped (← leanName "List") lean, .array ty)
  | .ref _ name [] =>
    let ctx ← get
    unless ctx.structs.any (·.name == name) do unsupportedType t
    return (structType ctx name, .struct name)
  | _ => unsupportedType t

/-! ### What statements do -/

def blockStatements : Stmt → List Stmt
  | .block _ body => body
  | s => [s]

/-- Every path through `statements` ends in a `return`. -/
partial def alwaysReturns (statements : List Stmt) : Bool :=
  match statements.getLast? with
  | some (.returnStmt ..) => true
  | some (.ifStmt _ _ thenBranch (some elseBranch)) =>
    alwaysReturns (blockStatements thenBranch) && alwaysReturns (blockStatements elseBranch)
  | _ => false

/-- `s` contains a `return`, `break` or `continue`. -/
partial def containsJump : Stmt → Bool
  | .returnStmt .. | .breakStmt _ | .continueStmt _ => true
  | .ifStmt _ _ t e => containsJump t || (e.map containsJump).getD false
  | .forOfStmt _ _ _ _ body | .whileStmt _ _ body => containsJump body
  | .block _ body => body.any containsJump
  | _ => false

/-- The names that `e` assigns, increments or pushes to. -/
partial def exprChanges : Expr → List String
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
    own ++ exprChanges callee ++ args.foldl (fun acc a => acc ++ exprChanges a) []
  | .array _ elems => elems.foldl (fun acc a => acc ++ exprChanges a) []
  | .object _ props => props.foldl (init := []) fun acc p =>
      match p with
      | .keyValue _ _ v => acc ++ exprChanges v
      | .shorthand .. => acc
  | .index _ a b | .binary _ _ a b => exprChanges a ++ exprChanges b
  | .cond _ a b c => exprChanges a ++ exprChanges b ++ exprChanges c
  | _ => []

partial def stmtChanges : Stmt → List String
  | .varDecl _ d => (d.init.map exprChanges).getD []
  | .exprStmt _ e => exprChanges e
  | .returnStmt _ v => (v.map exprChanges).getD []
  | .ifStmt _ test t e => exprChanges test ++ stmtChanges t ++ (e.map stmtChanges).getD []
  | .forOfStmt _ _ _ iterable body => exprChanges iterable ++ stmtChanges body
  | .whileStmt _ test body => exprChanges test ++ stmtChanges body
  | .block _ body => body.foldl (fun acc s => acc ++ stmtChanges s) []
  | _ => []

/-- The locals of `env` that `statements` change, in the order of `env`. -/
def changedNames (statements : List Stmt) (env : Env) : List String :=
  let changed := statements.foldl (fun acc s => acc ++ stmtChanges s) []
  (env.locals.filter fun l => changed.contains l.name).map (·.name)

def tuple (names : List String) : String :=
  match names with
  | [name] => name
  | _ => "(" ++ ", ".intercalate names ++ ")"

def indentBy (by_ : String) (lines : List String) : List String := lines.map (by_ ++ ·)

def indent (lines : List String) : List String := indentBy "  " lines

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
partial def isNonzeroBigintLiteral (e : Expr) : Bool :=
  match e.stripParens with
  | .unary _ .neg inner => isNonzeroBigintLiteral inner
  | .bigint _ text => bigintValue text != 0
  | _ => false

/-- `js` is how the output writes `JSNumber`. -/
def numberTest? (js : String) : String → Option (String → String)
  | "isSafeInteger" => some fun x => s!"({js}.toSafeInt {x}).isSome"
  | "isNaN" => some fun x => s!"({js}.isNaN {x})"
  | "isFinite" => some fun x => s!"({js}.isFinite {x})"
  | _ => none

def numberConstant? : String → Option String
  | "NaN" => some "nan"
  | "Infinity" => some "posInf"
  | _ => none

/-! ### Expressions -/

mutual

/-- `expected` is the type the context gives, which an object literal needs:
the return type, a declared type, a parameter type or a field type. -/
partial def translateExpr (env : Env) (expected : Option Ty) (e : Expr) : TM Code := do
  match e with
  | .paren _ inner => translateExpr env expected inner
  | .bigint _ text =>
    -- Typed, so Lean never defaults a numeral to `Nat`, where `0 - 1 = 0`.
    return ⟨s!"({bigintValue text} : {← leanName "Int"})", false, .bigint⟩
  | .number s text =>
    let some v := safeIntegerValue? text | reject s "a number literal must be a safe integer"
    return ⟨s!"({← leanName "JSNumber"}.ofSafeInt (N := {← numberVar}) ({v} : {← leanName "Int"}))", false, .number⟩
  | .null _ => return ⟨← leanName "none", false, .null⟩
  | .bool _ value => return ⟨if value then "true" else "false", false, .boolean⟩
  | .string _ value => return ⟨Sexp.quote value, false, .string⟩
  | .ident s name =>
    match env.lookup name with
    | none =>
      let some constant := numberConstant? name
        | reject s "only parameters and locals may be referenced"
      return ⟨s!"({← leanName "JSNumber"}.{constant} (N := {← numberVar}))", false, .number⟩
    | some l =>
      if l.binding == .array && !(← get).returning then
        reject s "an owned array may be read only in the return value"
      return ⟨name, false, l.type⟩
  | .member s obj name =>
    let o ← translateExpr env none obj
    let ctx : Ctx ← get
    let field? := match o.type with
      | .struct structName =>
        (ctx.structs.find? fun (i : StructInfo) => i.name == structName).bind
          fun info => info.fields.lookup name
      | _ => none
    let some type := field? | reject s "only fields of interfaces declared in this file may be read"
    let object := if obj matches .ident .. then o.code else s!"({o.code})"
    return ⟨s!"{object}.{name}", false, type⟩
  | .unary s op arg =>
    if op == .neg && (arg matches .ident _ "Infinity") && !env.has "Infinity" then
      return ⟨s!"({← leanName "JSNumber"}.negInf (N := {← numberVar}))", false, .number⟩
    let a ← translateExpr env none arg
    match op with
    | .not =>
      unless a.type == .boolean do reject s "'!' needs a boolean"
      return if a.prop then ⟨s!"¬({a.code})", true, .boolean⟩
        else ⟨s!"!({a.code})", false, .boolean⟩
    | .neg =>
      match a.type with
      | .bigint => return ⟨s!"(-{(← a.value)})", false, .bigint⟩
      | .number => return ⟨s!"({← leanName "JSNumber"}.neg {argument (← a.value)})", false, .number⟩
      | _ => reject s "unsupported unary operator"
    | _ => reject s "unsupported unary operator"
  | .binary s op l r => translateBinary env s op l r
  | .cond s test ifTrue ifFalse =>
    let c ← translateExpr env none test
    unless c.type == .boolean do reject test.span "a condition must be a boolean"
    let a ← translateExpr env expected ifTrue
    let b ← translateExpr env expected ifFalse
    let some type := a.type.join b.type | reject s "the branches of '?:' have different types"
    return ⟨s!"(if {c.code} then {(← a.value)} else {(← b.value)})", false, type⟩
  | .call s callee args => translateCall env s callee args
  | .object s props => translateObject env expected s props
  | _ => reject e.span "unsupported expression"

partial def translateCall (env : Env) (s : Span) (callee : Expr) (args : List Expr) : TM Code := do
  -- `Number.isNaN(x)` and the like. TypeScript lets them take any value; the
  -- model has them on numbers only.
  if let .member _ (.ident _ "Number") test := callee then
    if let (false, some form, [arg]) := (env.has "Number", numberTest? (← leanName "JSNumber") test, args) then
      let a ← translateExpr env none arg
      unless a.type == .number do
        reject arg.span s!"Number.{test} needs a number operand (narrow a nullable value first)"
      return ⟨form (argument (← a.value)), false, .boolean⟩
  let noCall {A : Type} : TM A :=
    reject s "calls may name only functions declared earlier in this file (no recursion)"
  let .ident _ name := callee | noCall
  let ctx ← get
  if (name == "isNaN" || name == "isFinite") && !ctx.functions.any (·.name == name) then
    reject s s!"the global {name} converts its argument to a number; use Number.{name}"
  let some fn := ctx.functions.find? (·.name == name) | noCall
  if env.has name then noCall
  unless fn.params.length == args.length do reject s s!"'{name}' takes {fn.params.length} arguments"
  -- Every def is generic over `N` when the file uses numbers. Name it, so
  -- that a callee whose signature does not mention `N` still elaborates.
  let mut parts := if ctx.usesNumber then #[name, s!"(N := {ctx.numberVar})"] else #[name]
  for (arg, paramType) in args.zip fn.params do
    let a ← translateExpr env (some paramType) arg
    unless a.type.assignableTo paramType do
      reject arg.span "the argument does not have the parameter's type"
    parts := parts.push (argument (← a.value))
  return ⟨"(" ++ " ".intercalate parts.toList ++ ")", false, fn.ret⟩

partial def translateObject (env : Env) (expected : Option Ty) (s : Span) (props : List Property) :
    TM Code := do
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
    let v ← translateExpr env (some fieldType) value
    unless v.type.assignableTo fieldType do reject span s!"'{key}' does not have the field's type"
    parts := parts.push s!"{key} := {(← v.value)}"
  for (field, _) in info.fields do
    unless seen.contains field do reject s s!"the object lacks the field '{field}'"
  return ⟨"({ " ++ ", ".intercalate parts.toList ++ " } : " ++ structType ctx structName ++ ")",
    false, .struct structName⟩

partial def translateBinary (env : Env) (s : Span) (op : BinOp) (l r : Expr) : TM Code := do
  -- `x === null` and `x !== null`: a test on a Lean `Option`.
  if (op == .strictEq || op == .strictNe) && ((l matches .null _) || (r matches .null _)) then
    let other := if l matches .null _ then r else l
    if other matches .null _ then reject s "compare null with a value, not with null"
    let isEquality := op == .strictEq
    -- Translate the operand even when the answer is fixed: translating is what
    -- refuses anything outside the subset, such as an assignment inside it.
    -- What the subset accepts has no side effects, so its value can be dropped.
    let o ← translateExpr env none other
    match o.type with
    | .nullable _ =>
      return ⟨s!"{argument o.code}.{if isEquality then "isNone" else "isSome"}", false, .boolean⟩
    | type =>
      -- Already narrowed: the answer is fixed, as it is in JS.
      return ⟨if isEquality == (type == .null) then "true" else "false", false, .boolean⟩
  -- `x === null || e` and `x !== null && e`: TypeScript narrows `x` in `e`,
  -- so Lean matches on `x` and binds it to the value inside.
  if let some (name, isNullTest, value) := nullTestOf env l then
    if (op == .or && isNullTest) || (op == .and && !isNullTest) then
      let whenSome ← translateExpr (env.narrow name value) none r
      unless whenSome.type == .boolean do reject r.span s!"'{op.symbol}' needs two booleans"
      let whenNone := if op == .or then "true" else "false"
      return ⟨s!"(match {name} with | {← leanName "none"} => {whenNone} | {← leanName "some"} {name} => {(← whenSome.value)})",
        false, .boolean⟩
  let a ← translateExpr env none l
  let b ← translateExpr env none r
  let bothBigInt := a.type == .bigint && b.type == .bigint
  let bothNumber := a.type == .number && b.type == .number
  let call (name : String) (x y : Code) (type : Ty) : TM Code := do
    return ⟨s!"({← leanName "JSNumber"}.{name} {argument (← x.value)} {argument (← y.value)})", false, type⟩
  let arithmetic (bigintOp numberOp : String) : TM Code := do
    if bothNumber then return ← call numberOp a b .number
    unless bothBigInt do reject s "arithmetic needs two bigints or two numbers"
    return ⟨s!"({(← a.value)} {bigintOp} {(← b.value)})", false, .bigint⟩
  -- `a > b` is `b < a`, and `a >= b` is `b <= a`.
  let compare (bigintOp numberOp : String) (swap : Bool) : TM Code := do
    if bothNumber then
      return ← if swap then call numberOp b a .boolean else call numberOp a b .boolean
    unless bothBigInt do reject s "ordering needs two bigints or two numbers"
    return ⟨s!"{(← a.value)} {bigintOp} {(← b.value)}", true, .boolean⟩
  let equal (negated : Bool) : TM Code := do
    if bothNumber then
      let eq ← call "eq" a b .boolean
      return if negated then { eq with code := "!" ++ eq.code } else eq
    if a.type.isObject || b.type.isObject || (a.type matches .nullable _) ||
        (b.type matches .nullable _) then
      reject s ("=== here would compare objects or nullable values; " ++
        "only primitives and null tests are supported")
    unless a.type == b.type && (a.type matches .boolean | .string | .bigint) do
      reject s "=== needs two values of the same primitive type"
    return ⟨s!"{(← a.value)} {if negated then "≠" else "="} {(← b.value)}", true, .boolean⟩
  -- bigint `/` truncates toward zero and `%` takes the sign of the dividend:
  -- Lean's `Int.tdiv` and `Int.tmod`. JS throws on a zero divisor, where Lean
  -- gives a value, so the divisor must be a nonzero literal.
  let divide (operation : String) : TM Code := do
    unless bothBigInt && isNonzeroBigintLiteral r do
      reject s "'/' and '%' need two bigints and a nonzero bigint literal divisor (JS throws on 0n)"
    requireFeature s .bigintDivision
    return ⟨s!"({← leanName "Int"}.{operation} {argument (← a.value)} {argument (← b.value)})", false, .bigint⟩
  let logical (propOp boolOp : String) : TM Code := do
    unless a.type == .boolean && b.type == .boolean do
      reject s s!"'{op.symbol}' needs two booleans"
    if a.prop && b.prop then return ⟨s!"({a.code}) {propOp} ({b.code})", true, .boolean⟩
    return ⟨s!"({(← a.value)} {boolOp} {(← b.value)})", false, .boolean⟩
  match op with
  | .add => arithmetic "+" "add"
  | .sub => arithmetic "-" "sub"
  | .mul => arithmetic "*" "mul"
  | .div => divide "tdiv"
  | .mod => divide "tmod"
  | .lt => compare "<" "lt" false
  | .le => compare "≤" "le" false
  | .gt => compare ">" "lt" true
  | .ge => compare "≥" "le" true
  | .strictEq => equal false
  | .strictNe => equal true
  | .and => logical "∧" "&&"
  | .or => logical "∨" "||"
  | _ => reject s "unsupported binary operator"

end

/-! ### Statements -/

def assignOps? : AssignOp → Option (String × String)
  | .add => some ("+", "add")
  | .sub => some ("-", "sub")
  | .mul => some ("*", "mul")
  | _ => none

/-- One mutation statement, as the local it changes and its new value. -/
def translateUpdate (env : Env) (s : Span) (e : Expr) : TM (String × String) := do
  let refuse {A : Type} : TM A :=
    reject s "an expression statement must assign a let local or push to an owned array"
  match e with
  | .call _ (.member _ (.ident _ target) "push") args =>
    let refusePush {A : Type} : TM A :=
      reject s "push is allowed only onto an owned array, one element at a time"
    let some { binding := .array, type := .array elemType, .. } := env.lookup target | refusePush
    let [element] := args | refusePush
    let v ← translateExpr env (some elemType) element
    unless v.type.assignableTo elemType do
      reject element.span "the element does not have the array's element type"
    return (target, s!"{target} ++ [{(← v.value)}]")
  | .assign _ op (.ident _ name) right =>
    unless op matches .assign | .add | .sub | .mul do refuse
    let some { binding := .«let», type, .. } := env.lookup name
      | reject s "only a local declared with let may be assigned"
    let v ← translateExpr env (some type) right
    match assignOps? op with
    | none =>
      unless v.type.assignableTo type do reject s "the value does not have the local's type"
      return (name, (← v.value))
    | some (bigintOp, numberOp) =>
      -- On `number` the operation goes through the abstract number model.
      if type == .number && v.type == .number then
        return (name, s!"({← leanName "JSNumber"}.{numberOp} {name} {argument (← v.value)})")
      unless type == .bigint && v.type == .bigint do
        reject s "arithmetic needs two bigints or two numbers"
      return (name, s!"{name} {bigintOp} {(← v.value)}")
  | _ => refuse

mutual

partial def translateStatements (env : Env) (tail : Tail) : List Stmt → TM (List String)
  | [] => do
    match tail with
    | .ret =>
      let ctx ← get
      throw s!"{ctx.file}: '{ctx.currentFunction}' can end without a return"
    | .state names => return [tuple names]
  | stmt :: rest => do
    match stmt with
    | .returnStmt s value =>
      let (.ret, [], some v) := (tail, rest, value)
        | reject s "return must be the last statement of a function and carry a value"
      modify fun c => { c with returning := true }
      let returnType := (← get).returnType
      let code ← translateExpr env (some returnType) v
      unless code.type.assignableTo returnType do
        reject v.span "the value does not have the function's return type"
      modify fun c => { c with returning := false }
      return [(← code.value)]
    | .varDecl s d => translateVariable env s d rest tail
    | .exprStmt s e =>
      let (name, update) ← translateUpdate env s e
      return s!"let {name} := {update}" :: (← translateStatements env tail rest)
    | .ifStmt s test thenBranch elseBranch =>
      translateIf env s test thenBranch elseBranch rest tail
    | .forOfStmt s kind name iterable body =>
      translateForOf env s kind name iterable body rest tail
    | _ => reject stmt.span "unsupported statement"

partial def translateVariable (env : Env) (s : Span) (d : VarDecl) (rest : List Stmt)
    (tail : Tail) : TM (List String) := do
  let some init := d.init | reject s "declare one const or let identifier with an initializer"
  if let .array _ elems := init then
    let refuse {A : Type} : TM A := reject s "an owned array must be 'const x: Array<T> = []'"
    unless d.kind == .const && elems.isEmpty do refuse
    let some annotation := d.type | refuse
    let (lean, type) ← translateType annotation
    unless type matches .array _ do refuse
    let env' ← declare env s d.name .array type
    return s!"let {d.name} : {lean} := []" :: (← translateStatements env' tail rest)
  let declared ← match d.type with
    | some annotation => some <$> Prod.snd <$> translateType annotation
    | none => pure none
  let code ← translateExpr env declared init
  let type ← match declared with
    | some t =>
      if code.type.assignableTo t then pure t
      else reject s "the value does not have the declared type"
    | none => pure code.type
  let binding := if d.kind == .const then Binding.const else .«let»
  let env' ← declare env s d.name binding type
  return s!"let {d.name} := {(← code.value)}" :: (← translateStatements env' tail rest)

partial def translateIf (env : Env) (s : Span) (test : Expr) (thenBranch : Stmt)
    (elseBranch : Option Stmt) (rest : List Stmt) (tail : Tail) : TM (List String) := do
  let thenStatements := blockStatements thenBranch
  let elseStatements := (elseBranch.map blockStatements).getD []
  -- `if (x === null)` and `if (x !== null)`: TypeScript narrows `x` in each
  -- branch, so Lean matches on `x` and binds it to the value.
  let nullTest := nullTestOf env test
  let (envTrue, envFalse) := match nullTest with
    | some (name, true, value) => (env.narrow name .null, env.narrow name value)
    | some (name, false, value) => (env.narrow name value, env.narrow name .null)
    | none => (env, env)
  let branch (whenTrue whenFalse : List String) : TM (List String) := do
    match nullTest with
    | none =>
      let c ← translateExpr env none test
      unless c.type == .boolean do reject test.span "a condition must be a boolean"
      return [s!"if {c.code} then"] ++ indent whenTrue ++ ["else"] ++ indent whenFalse
    | some (name, isNullTest, _) =>
      return [s!"match {name} with", s!"| {← leanName "none"} =>"] ++
        indent (if isNullTest then whenTrue else whenFalse) ++
        [s!"| {← leanName "some"} {name} =>"] ++ indent (if isNullTest then whenFalse else whenTrue)
  if (tail matches .ret) && alwaysReturns thenStatements then
    if elseBranch.isSome && !rest.isEmpty then
      reject s "code after an if whose branches both return is unreachable"
    let whenTrue ← translateStatements envTrue tail thenStatements
    let whenFalse ← translateStatements envFalse tail (elseStatements ++ rest)
    return (← branch whenTrue whenFalse)
  if (thenStatements ++ elseStatements).any containsJump then
    reject s "a branch that does not always return may not return, break or continue"
  let names := changedNames (thenStatements ++ elseStatements) env
  if names.isEmpty then reject s "an if without a return must change a local"
  if let some (name, _, _) := nullTest then
    if names.contains name then
      reject s "a local tested against null may not be assigned in that if"
  let state := Tail.state names
  let whenTrue ← translateStatements envTrue state thenStatements
  let whenFalse ← translateStatements envFalse state elseStatements
  let lines ← branch whenTrue whenFalse
  return [s!"let {tuple names} :="] ++ indent lines ++ (← translateStatements env tail rest)

partial def translateForOf (env : Env) (s : Span) (kind : VarKind) (element : String)
    (iterable : Expr) (body : Stmt) (rest : List Stmt) (tail : Tail) : TM (List String) := do
  unless kind == .const do reject s "a loop must be 'for (const x of xs)'"
  let bodyStatements := blockStatements body
  if bodyStatements.any containsJump then reject s "a loop body may not return, break or continue"
  let names := changedNames bodyStatements env
  if names.isEmpty then reject s "a loop must change a local"
  let items ← translateExpr env none iterable
  let .array elemType := items.type | reject iterable.span "a loop must run over an array"
  let bodyEnv ← declare env s element .const elemType
  let bodyLines ← translateStatements bodyEnv (.state names) bodyStatements
  let lastLine := bodyLines.getLast?.getD ""
  return [s!"let {tuple names} :=", s!"  {← leanName "List.foldl"}", s!"    (fun {tuple names} {element} =>"] ++
    indentBy "      " (bodyLines.dropLast ++ [lastLine ++ ")"]) ++
    [s!"    {tuple names} {items.code}"] ++ (← translateStatements env tail rest)

end

/-! ### Declarations -/

def declareTopLevel (s : Span) (name : String) : TM Unit := do
  let ctx ← get
  if ctx.structs.any (·.name == name) || ctx.functions.any (·.name == name) then
    reject s s!"'{name}' is declared twice"

def translateInterface (s : Span) (name : String) (fields : List Field) : TM String := do
  let name ← checkName s name
  declareTopLevel s name
  let ctx ← get
  let mut infos := #[]
  let mut lines := #[s!"structure {name}{if ctx.usesNumber then s!" ({ctx.numberVar} : Type)" else ""} where"]
  for f in fields do
    unless f.readonly && !f.optional do
      reject f.span "interface fields must be readonly, required and typed"
    let field ← checkName f.span f.name
    if infos.any (·.1 == field) then reject f.span s!"'{field}' is declared twice"
    let (lean, type) ← translateType f.type
    infos := infos.push (field, type)
    lines := lines.push s!"  {field} : {lean}"
  modify fun c => { c with structs := c.structs ++ [{ name, fields := infos.toList }] }
  return "\n".intercalate lines.toList

def translateFunction (s : Span) (name : String) (params : List Param)
    (returnType : Option TypeExpr) (body : Stmt) : TM String := do
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
    let (lean, ty) ← translateType type
    env := env.add { name := paramName, binding := .param, type := ty }
    leanParams := leanParams.push s!"({paramName} : {lean})"
    types := types.push ty
  let (leanReturn, ret) ← translateType returnType
  modify fun c => { c with currentFunction := name, returnType := ret }
  let lines ← translateStatements env .ret (blockStatements body)
  modify fun c => { c with functions := c.functions ++ [{ name, params := types.toList, ret }] }
  let n ← numberVar
  let js ← leanName "JSNumber"
  let generic := if (← get).usesNumber then s!" \{{n} : Type} [{js} {n}]" else ""
  return "\n".intercalate
    (s!"def {name}{generic} {" ".intercalate leanParams.toList} : {leanReturn} :=" :: indent lines)

/-! ### The number model -/

def isNumberName (name : String) : Bool :=
  name == "Number" || name == "NaN" || name == "Infinity"

partial def typeUsesNumber : TypeExpr → Bool
  | .keyword _ name => name == "number"
  | .literal _ (.number _) => true
  | .ref _ name args => isNumberName name || args.any typeUsesNumber
  | .array _ e | .paren _ e => typeUsesNumber e
  | .union _ members => members.any typeUsesNumber
  | _ => false

partial def exprUsesNumber : Expr → Bool
  | .ident _ name => isNumberName name
  | .number .. => true
  | .member _ obj name => isNumberName name || exprUsesNumber obj
  | .object _ props => props.any fun
    | .shorthand _ name => isNumberName name
    | .keyValue _ key value =>
      (match key with
        | .ident name => isNumberName name
        | .number _ => true
        | .string _ => false) || exprUsesNumber value
  | .array _ es => es.any exprUsesNumber
  | .call _ f args => exprUsesNumber f || args.any exprUsesNumber
  | .paren _ e | .unary _ _ e | .prefix _ _ e | .postfix _ _ e => exprUsesNumber e
  | .index _ a b | .binary _ _ a b | .assign _ _ a b => exprUsesNumber a || exprUsesNumber b
  | .cond _ a b c => exprUsesNumber a || exprUsesNumber b || exprUsesNumber c
  | _ => false

def varUsesNumber (d : VarDecl) : Bool :=
  isNumberName d.name || (d.type.map typeUsesNumber).getD false ||
    (d.init.map exprUsesNumber).getD false

partial def stmtUsesNumber : Stmt → Bool
  | .varDecl _ d => varUsesNumber d
  | .exprStmt _ e => exprUsesNumber e
  | .returnStmt _ v => (v.map exprUsesNumber).getD false
  | .ifStmt _ test t e =>
    exprUsesNumber test || stmtUsesNumber t || (e.map stmtUsesNumber).getD false
  | .forOfStmt _ _ name iterable body =>
    isNumberName name || exprUsesNumber iterable || stmtUsesNumber body
  | .whileStmt _ test body => exprUsesNumber test || stmtUsesNumber body
  | .block _ body => body.any stmtUsesNumber
  | _ => false

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

/-- Translate `source`, the TypeScript file `file`, to a Lean file whose
definitions are in namespace `ns`, for code that runs on the edition
`target`. -/
def translate (file source ns : String) (target : Edition := .default) :
    Except String String := do
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
  let ctx : Ctx :=
    { file, target, src, lineStarts := lineStarts src, usesNumber := moduleUsesNumber m,
      clashes := leanNames.map (·.1) |>.filter idents.contains,
      numberVar := numberVar.getD "N" }
  let sections : TM (List String) := m.decls.mapM fun
    | .interface s _ name fields => translateInterface s name fields
    | .function s _ name params ret body => translateFunction s name params ret body
    | d => reject d.span "only interfaces and functions may appear at top level"
  match sections.run ctx with
  | .error e _ => .error e
  | .ok sections ctx =>
    let header :=
      if ctx.usesNumber then ["import tolean.TypeScript.Spec.Number", "", "open tolean.TypeScript"]
      else []
    return "\n".intercalate
      ([s!"-- Generated by tolean {version} for {target.name} from {file}. Do not edit."] ++
        header ++
        [s!"namespace {ns}", "", "\n\n".intercalate sections, "", s!"end {ns}", ""])

end tolean.TypeScript.Translate
