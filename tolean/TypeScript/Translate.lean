import tolean.Sexp
import tolean.Version
import tolean.TypeScript.Edition
import tolean.TypeScript.Syntax.Parser
import tolean.TypeScript.IR
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

The translator does not write text. It builds the Tolean IR (`IR.lean`),
and the printer there writes it. So the translator is a function from a
syntax tree to the IR, which a theorem can be about.
-/
namespace tolean.TypeScript.Translate

open tolean tolean.TypeScript.Syntax

/-- A type of the subset, after narrowing. -/
inductive Ty where
  | bigint | number | boolean | string | null
  /-- `T | null`, where `T` is not `null` and not nullable. -/
  | nullable (value : Ty)
  /-- The value of an optional field `f?: T`: a `T`, or `undefined` when the
  object has no such field. `T` is neither nullable nor optional. -/
  | optional (value : Ty)
  | array (elem : Ty)
  /-- An interface of the program: one that the file declares, or one that it
  imports. -/
  | struct (ref : DeclRef)
  /-- A literal union of strings, `type T = 'a' | 'b'`, of the program. -/
  | enum (ref : DeclRef)
  /-- A tagged union of interfaces of the program, `type T = A | B`, narrowed
  to the members with the tags `tags`. -/
  | tagged (ref : DeclRef) (tags : List String)
  /-- The type of a tag field, one string literal such as `'circle'`. -/
  | literal (value : String)
deriving BEq, Repr, Inhabited

/-- A value of type `source` can stand where `target` is expected. Arrays and
structures must match exactly. -/
def Ty.assignableTo (source target : Ty) : Bool :=
  source == target ||
    match target with
    | .nullable value => source == .null || source == value
    -- A union narrowed to some of its members is a value of the union.
    | .tagged ref tags =>
      match source with
      | .tagged ref' tags' => ref' == ref && tags'.all tags.contains
      | _ => false
    | _ => false

/-- The type of `c ? a : b`. -/
def Ty.join (a b : Ty) : Option Ty :=
  if a == b then some a
  else match a, b with
    | .null, .nullable t | .nullable t, .null => some (.nullable t)
    | .nullable t, u | u, .nullable t => if t == u then some (.nullable t) else none
    -- The output has one `none` for both `undefined` and `null`, so it cannot
    -- hold a value that may be either.
    | .null, .optional _ | .optional _, .null => none
    | .null, t | t, .null => some (.nullable t)
    | _, _ => none

/-- The type of the value that an optional field holds when it is set. -/
def Ty.unoptional : Ty → Ty
  | .optional t => t
  | t => t

/-- `T | null`. -/
def Ty.isNullable : Ty → Bool
  | .nullable _ => true
  | _ => false

/-- A primitive that `===` compares by value and the output compares with `=`. -/
def Ty.isEqPrimitive : Ty → Bool
  | .boolean | .string | .bigint | .enum _ => true
  | _ => false

/-- An object, which `===` compares by identity. -/
def Ty.isObject : Ty → Bool
  | .array _ | .struct _ | .tagged .. => true
  | _ => false

/-- What `typeof` gives for a value of type `t`, when `t` is a primitive type
that a union of primitive types may have as a member. -/
def Ty.typeOf? : Ty → Option String
  | .bigint => some "bigint"
  | .number => some "number"
  | .boolean => some "boolean"
  | .string => some "string"
  | _ => none

/-- The Lean type that the output gives a value of type `t`. -/
def Ty.lean : Ty → IR.Ty
  | .bigint => .int
  | .number => .number
  | .boolean => .bool
  | .string => .string
  | .null => .null
  | .nullable t => .option t.lean
  | .optional t => .optional t.lean
  | .array t => .list t.lean
  | .struct ref => .struct ref
  | .enum ref => .enum ref
  | .tagged ref _ => .tagged ref
  | .literal value => .tag value

/-- A tagged union of the program, with the file that declares it: a union
of interfaces, `type T = A | B`, or a union of primitive types,
`type T = string | bigint`. `members` maps each tag to the type of its
member. Each interface of a union of interfaces has the field `field`, whose
type is one string literal, the tag. A union of primitive types has no
`field`, and the tag of each member is the `typeof` of its values. -/
structure UnionInfo where
  file : String
  name : String
  exported : Bool := false
  field : Option String
  members : List (String × Ty)

def UnionInfo.ref (i : UnionInfo) : DeclRef := ⟨i.file, i.name⟩

/-- How a name in scope may be used. Only `let` and `array` locals change. -/
inductive Binding where
  | param | const | «let» | array
deriving BEq, Repr, Inhabited

structure Local where
  name : String
  binding : Binding
  type : Ty

/-- An interface of the program, with the file that declares it. -/
structure StructInfo where
  file : String
  name : String
  exported : Bool := false
  fields : List (String × Ty)
  /-- For `type T = Record<K, V>`, the literal union `K`, whose strings are
  the fields. An index `r[k]` with a key of type `K` reads one. -/
  key : Option DeclRef := none

def StructInfo.ref (i : StructInfo) : DeclRef := ⟨i.file, i.name⟩

/-- A function of the program, with the file that declares it. -/
structure FnInfo where
  file : String
  name : String
  exported : Bool := false
  params : List Ty
  ret : Ty

def FnInfo.ref (f : FnInfo) : DeclRef := ⟨f.file, f.name⟩

/-- The names in scope, in the order they were declared, and the functions
that a call may name. -/
structure Env where
  locals : List Local := []
  functions : List FnInfo := []
  /-- The tagged unions whose tags a test may read. -/
  unions : List UnionInfo := []

def Env.lookup (env : Env) (name : String) : Option Local := env.locals.find? (·.name == name)

def Env.has (env : Env) (name : String) : Bool := (env.lookup name).isSome

def Env.add (env : Env) (l : Local) : Env := { env with locals := env.locals ++ [l] }

/-- `name` has the type `type` from here on, as after `x !== null`. -/
def Env.narrow (env : Env) (name : String) (type : Ty) : Env :=
  { env with locals := env.locals.map fun l => if l.name == name then { l with type } else l }

/-- A literal union of strings of the program, `type T = 'a' | 'b'`, with the
file that declares it and its strings in the order of the source. -/
structure EnumInfo where
  file : String
  name : String
  exported : Bool := false
  members : List String

def EnumInfo.ref (i : EnumInfo) : DeclRef := ⟨i.file, i.name⟩

/-- A type alias of the program, `type T = U`, with the file that declares
it. `type` is the type of `U`, which the translator writes wherever the
source names `T`. -/
structure AliasInfo where
  file : String
  name : String
  exported : Bool := false
  type : Ty

/-- What a file offers the files that import from it: its exported functions,
interfaces and type aliases, and whether its declarations are generic over
the number type. -/
structure Interface where
  functions : List FnInfo := []
  structs : List StructInfo := []
  aliases : List AliasInfo := []
  enums : List EnumInfo := []
  unions : List UnionInfo := []
  usesNumber : Bool := false
  /-- The name under which its declarations bind the number type. -/
  numberVar : String := "N"
  /-- The edition that it is translated for. A file may import from it only
  when the file's own edition is at least as new. -/
  target : Edition := .default

structure Ctx where
  file : String
  /-- The edition the code runs on. A feature newer than it is refused. -/
  target : Edition
  src : Array Char
  lineStarts : Array Nat
  structs : List StructInfo := []
  /-- The type aliases that the file declares or imports. -/
  aliases : List AliasInfo := []
  /-- The literal unions that the file declares or imports. -/
  enums : List EnumInfo := []
  /-- The tagged unions that the file declares or imports. -/
  unions : List UnionInfo := []
  functions : List FnInfo := []
  /-- The files that this file may import from, by path. -/
  interfaces : List (String × Interface) := []
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

/-- The interfaces whose fields the file may read or build: its own and the
ones it imports, and the exported interfaces of the files before it. A value
of an interface that the file does not import can reach it through a field
of one that it does. -/
def Ctx.knownStructs (c : Ctx) : List StructInfo :=
  c.structs ++ c.interfaces.flatMap (·.2.structs)

/-- The literal unions whose strings the file may write: its own and the ones
it imports, and the exported ones of the files before it, which can reach it
through a field. -/
def Ctx.knownEnums (c : Ctx) : List EnumInfo :=
  c.enums ++ c.interfaces.flatMap (·.2.enums)

/-- The tagged unions whose values the file may build and test, as
`knownStructs` has the interfaces. -/
def Ctx.knownUnions (c : Ctx) : List UnionInfo :=
  c.unions ++ c.interfaces.flatMap (·.2.unions)

/-- A translated expression. `prop` is true when the code is a Lean `Prop`,
not a `Bool`. -/
structure Code where
  code : IR.Expr
  prop : Bool
  type : Ty

/-- In value position, a `Prop` becomes a `Bool` with `decide`. -/
def Code.value (c : Code) : IR.Expr :=
  if c.prop then .decide c.code else c.code

/-- `c` where the context expects a value of type `expected`. A value of a
member of a union of primitive types, such as a `string` where
`string | bigint` is expected, becomes the member's constructor. In JS the
value stays the same. -/
def Code.into (unions : List UnionInfo) (c : Code) (expected : Option Ty) : Code :=
  match expected with
  | some (.tagged ref tags) | some (.nullable (.tagged ref tags)) =>
    match c.type.typeOf? with
    | some k =>
      if (unions.any fun u => u.ref == ref && u.field.isNone) && tags.contains k then
        ⟨.inject ref k c.value, false, .tagged ref tags⟩
      else c
    | none => c
  | _ => c

/-- What a statement list ends in: a `return`, or the tuple of changed locals. -/
inductive Tail where
  | ret
  | state (names : List String)

def Tail.isRet : Tail → Bool
  | .ret => true
  | .state _ => false

def leanReserved : List String := IR.leanReserved

/-! ### Literal values

The translator reads a literal with the interpreter's own functions,
`Eval.bigintLiteral` and `Eval.numberLiteral`, so the two cannot disagree on
its value. -/

/-- The value of a bigint literal, such as `0xffn`. -/
def bigintValue? (text : String) : Option Int := Eval.bigintLiteral text

/-- The safe integer that a number literal denotes exactly, or none. A literal
such as `0.5`, or one above `2^53 - 1`, has none. -/
def safeIntegerValue? (text : String) : Option Int := Eval.numberLiteral text

/-! ### Errors -/

/-- The source text of `span`, at most 80 characters, without the spaces
that the cut may leave at its end. A message never ends in a space, so the
native command and the WebAssembly build give the same text whether or not
their caller trims it. -/
def spanText (ctx : Ctx) (span : Span) : String :=
  let index (p : Pos) : Nat := (ctx.lineStarts[p.line - 1]?.getD 0) + p.col - 1
  let first := index span.start
  let last := min (index span.stop) (first + 80)
  ((ctx.src.extract first last).foldl String.push "").trimAsciiEnd.toString

def reject {A : Type} (span : Span) (reason : String) : TM A := do
  let ctx ← get
  throw s!"{ctx.file}:{span.start.line}:{span.start.col}: {reason}: {spanText ctx span}"

/-- The program nests deeper than `Ctx.fuel` allows. -/
def tooDeep {A : Type} : TM A := do
  throw s!"{(← get).file}: the program is nested too deeply for the translator"

/-- `Ctx.fuel`, for a call into the translator from outside it. -/
def fuelLimit : TM Nat := do return (← get).fuel

/-- The value inside `o`, or a refusal at `span`. A proof about the translator
reads `orReject` through `orReject_ok`, which it cannot do for a
`let some x := o | reject …`. -/
def orReject {A : Type} (o : Option A) (span : Span) (reason : String) : TM A :=
  match o with
  | some a => pure a
  | none => reject span reason

/-- Refuse the node at `span` unless the target edition has `f`. -/
def requireFeature (span : Span) (f : Feature) : TM Unit := do
  let target := (← get).target
  unless target.supports f do reject span (f.refusal target)

/-- The globals that the subset reads by name. A file that names one of them
needs the number type. -/
def isNumberName (name : String) : Bool :=
  name == "Number" || name == "NaN" || name == "Infinity"

/-- The globals that the subset reads by name, so that no declaration may
hide them. -/
def isGlobalName (name : String) : Bool :=
  isNumberName name || name == "undefined"

def checkName (span : Span) (name : String) : TM String := do
  if leanReserved.contains name then reject span s!"name '{name}' is reserved in Lean"
  return name

/-- The name of a parameter or a local. TypeScript keeps types and values
apart, but Lean does not, and the output writes an interface of the file by
its bare name. So a local with that name would hide the interface. -/
def checkLocalName (span : Span) (name : String) : TM String := do
  let ctx ← get
  if ctx.structs.any fun i => i.name == name && i.file == ctx.file then
    reject span s!"'{name}' would hide the interface {name} in Lean; choose another name"
  if (ctx.enums.any fun i => i.name == name && i.file == ctx.file) ||
      (ctx.unions.any fun i => i.name == name && i.file == ctx.file) then
    reject span s!"'{name}' would hide the type {name} in Lean; choose another name"
  checkName span name

def declare (env : Env) (span : Span) (name : String) (binding : Binding) (type : Ty) :
    TM Env := do
  if env.has name then reject span s!"'{name}' shadows a name already in scope"
  -- A local is in its temporal dead zone from the start of its block, so a
  -- use of the name before the declaration throws in JS. The subset reads
  -- such a use as the function or the global, so it refuses the local.
  if env.functions.any (·.name == name) || isGlobalName name then
    reject span s!"'{name}' would hide the function or global {name} in its whole block; choose another name"
  let _ ← checkLocalName span name
  -- A local of type `null` is always `null`, and Lean gives it the type
  -- `Option Empty`, which no other value of a nullable type has.
  if type == .null then reject span s!"'{name}' is always null; declare its type, such as bigint | null"
  return env.add { name, binding, type }

/-! ### Types -/

def unsupportedType {A : Type} (t : TypeExpr) : TM A :=
  reject t.span
    ("unsupported type (use bigint, number, boolean, string, T | null, arrays, " ++
      "or an interface or type declared above)")

/-- The strings of a literal union of strings, `'a' | 'b'`, or of one string
literal type. -/
def stringLiterals : TypeExpr → Option (List String)
  | .literal _ (.string v) => some [v]
  | .paren _ t => stringLiterals t
  | .union _ members => members.mapM fun
    | .literal _ (.string v) => some v
    | _ => none
  | _ => none

/-- The primitive types that a union of primitive types may have as members,
by the `typeof` of their values. -/
def primitiveType? : String → Option Ty
  | "bigint" => some .bigint
  | "number" => some .number
  | "boolean" => some .boolean
  | "string" => some .string
  | _ => none

/-- The keywords of a union of primitive types, such as `string | bigint`. -/
def primitiveMembers : TypeExpr → Option (List String)
  | .union _ members => members.mapM fun
    | .keyword _ k => if (primitiveType? k).isSome then some k else none
    | _ => none
  | _ => none

/-- The type of `t` in the subset. The output writes it as `Ty.lean`. -/
def translateType (t : TypeExpr) : TM Ty := do
  -- The output needs a name for the inductive type of a literal union, and of
  -- a union of primitive types.
  if (stringLiterals t).isSome then
    reject t.span "a literal union needs a name; declare it as a type, such as type T = 'a' | 'b'"
  if (primitiveMembers t).isSome then
    reject t.span
      "a union of primitive types needs a name; declare it as a type, such as type T = string | bigint"
  if let .union s members := t then
    let rest := members.filter fun m => !(m matches .null _)
    if rest.length ≥ 2 && rest.length < members.length && (primitiveMembers (.union s rest)).isSome then
      reject t.span ("a union of primitive types and null needs a name for its primitive types; " ++
        "declare type T = string | bigint and write T | null")
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
    | .null _, value | value, .null _ =>
      -- `Maybe | null`, where the alias `Maybe` is nullable already, is
      -- `Maybe`, as in TypeScript.
      match ← translateType value with
      | .nullable t => return .nullable t
      | t => return .nullable t
    | _, _ => unsupportedType t
  | .array _ elem => return .array (← translateType elem)
  | .ref _ "Record" [_, _] | .ref _ "Readonly" [.ref _ "Record" [_, _]] =>
    reject t.span "a Record type needs a name; declare it as a type, such as type T = Record<K, V>"
  | .ref _ name [elem] =>
    unless name == "Array" || name == "ReadonlyArray" do unsupportedType t
    return .array (← translateType elem)
  | .ref _ name [] =>
    let ctx ← get
    match ctx.structs.find? (·.name == name) with
    | some info => return .struct info.ref
    | none =>
      match ctx.enums.find? (·.name == name) with
      | some info => return .enum info.ref
      | none =>
        match ctx.unions.find? (·.name == name) with
        | some info => return .tagged info.ref (info.members.map (·.1))
        | none =>
          match ctx.aliases.find? (·.name == name) with
          | some info => return info.type
          | none => unsupportedType t
  | _ => unsupportedType t

/-! ### What statements do -/

def blockStatements : Stmt → List Stmt
  | .block _ body => body
  | s => [s]

/-- The clause ends in `break`. -/
def endsInBreak : List Stmt → Bool
  | [] => false
  | [s] => s.isBreak
  | _ :: rest => endsInBreak rest

/-- The statements of a clause without the `break` it ends in. -/
def dropBreak : List Stmt → List Stmt
  | [] => []
  | [s] => if s.isBreak then [] else [s]
  | s :: rest => s :: dropBreak rest

mutual

-- Each call is on a part of its argument, so the recursion is structural and
-- the kernel can run it, as a certificate's check of the translation needs.

/-- Every path through `statements` ends in a `return`. -/
def alwaysReturns : List Stmt → Bool
  | [] => false
  | s :: rest => if rest.isEmpty then endsInReturn s else alwaysReturns rest

/-- `s`, the last statement of a list, ends every path in a `return`. -/
def endsInReturn : Stmt → Bool
  | .returnStmt .. => true
  | .ifStmt _ _ thenBranch (some elseBranch) => branchReturns thenBranch && branchReturns elseBranch
  | _ => false

/-- `alwaysReturns (blockStatements s)`. -/
def branchReturns : Stmt → Bool
  | .block _ body => alwaysReturns body
  | .returnStmt .. => true
  | .ifStmt _ _ thenBranch (some elseBranch) => branchReturns thenBranch && branchReturns elseBranch
  | _ => false

end

mutual

/-- `s` contains a `return`, `break` or `continue`. -/
def containsJump : Stmt → Bool
  | .returnStmt .. | .breakStmt _ | .continueStmt _ => true
  | .ifStmt _ _ t (some e) => containsJump t || containsJump e
  | .ifStmt _ _ t none => containsJump t
  | .forOfStmt _ _ _ _ body | .whileStmt _ _ body => containsJump body
  | .block _ body => anyContainsJump body
  | .switchStmt _ _ clauses => clausesContainJump clauses
  | _ => false

def anyContainsJump : List Stmt → Bool
  | [] => false
  | s :: rest => containsJump s || anyContainsJump rest

/-- The statements of a clause contain a jump, apart from the `break` they
end in, which leaves only the `switch`. -/
def clauseContainsJump : List Stmt → Bool
  | [] => false
  | [s] => !s.isBreak && containsJump s
  | s :: rest => containsJump s || clauseContainsJump rest

def clausesContainJump : List (Option Expr × List Stmt) → Bool
  | [] => false
  | (_, body) :: rest => clauseContainsJump body || clausesContainJump rest

end

mutual

/-- The names that `e` assigns, increments or pushes to. -/
def exprChanges : Expr → List String
  | .assign _ op target value =>
    let own := match target with
      | .ident _ name => if op.isSimple || op == .coalesce then [name] else []
      | _ => []
    own ++ exprChanges target ++ exprChanges value
  | .prefix _ _ (.ident _ name) | .postfix _ _ (.ident _ name) => [name]
  | .prefix _ _ e | .postfix _ _ e | .paren _ e | .unary _ _ e | .member _ e _ | .optMember _ e _ =>
    exprChanges e
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
  | .switchStmt _ disc clauses => exprChanges disc ++ clausesChanges clauses
  | _ => []

def stmtsChanges : List Stmt → List String
  | [] => []
  | s :: rest => stmtChanges s ++ stmtsChanges rest

def clausesChanges : List (Option Expr × List Stmt) → List String
  | [] => []
  | (test, body) :: rest => optionChanges test ++ stmtsChanges body ++ clausesChanges rest

end

/-- The locals of `env` that `statements` change, in the order of `env`. -/
def changedNames (statements : List Stmt) (env : Env) : List String :=
  let changed := stmtsChanges statements
  (env.locals.filter fun l => changed.contains l.name).map (·.name)

/-- The operators that can test a value against `null`: `some true` for `===`
and `==`, and `some false` for `!==` and `!=`. In the subset `==` and `===`
agree on such a test, because no value is `undefined` (`Eval.looseEq`). -/
def nullOp? : BinOp → Option Bool
  | .strictEq | .looseEq => some true
  | .strictNe | .looseNe => some false
  | _ => none

/-- `x === null` or `x !== null`, or the same with `==` and `!=`, where `x`
is a name in scope that may be `null` here: `(x, the test is equality, the
type of x when not null)`. A name already narrowed is not an `Option` in Lean
any more, so it gets no `match`. -/
def nullTestOf (env : Env) (e : Expr) : Option (String × Bool × Ty) :=
  match e.stripParens with
  | .binary _ op l r =>
    match nullOp? op with
    | none => none
    | some isEquality =>
      let other? := if r.isNull then some l else if l.isNull then some r else none
      match other? with
      | some (.ident _ name) =>
        match env.lookup name with
        | some { type := .nullable value, .. } => some (name, isEquality, value)
        | _ => none
      | _ => none
  | _ => none

/-- The tag that an object literal sets: the string of its property `field`. -/
def tagOfProps (field : String) (props : List Property) : Option String :=
  props.findSome? fun
    | .keyValue _ (.ident k) (.string _ v) => if k == field then some v else none
    | _ => none

/-- A test of the tag of a tagged union, as `x.kind === 'circle'` or
`typeof x === 'string'` reads it: the local, the union, its tag field and
the tag, whether the test is `===`, and the types of the local where the tag
matches and where it does not. A test of `typeof` has no tag field. When one
member is left where the tag does not match, `other` is its tag. -/
structure TagTest where
  name : String
  ref : DeclRef
  field : Option String
  tag : String
  isEq : Bool
  whenTag : Ty
  whenOther : Ty
  other : Option String

/-- The local, the field and the string of `x.kind` and `'circle'`, or the
local and the string of `typeof x` and `'string'`, in either order. -/
def tagSide (l r : Expr) : Option (String × Option String × String) :=
  match l, r with
  | .member _ (.ident _ n) f, .string _ t => some (n, some f, t)
  | .string _ t, .member _ (.ident _ n) f => some (n, some f, t)
  | .unary _ .typeof (.ident _ n), .string _ t => some (n, none, t)
  | .string _ t, .unary _ .typeof (.ident _ n) => some (n, none, t)
  | _, _ => none

/-- The type of a local of the union `ref` where its tag is none of the one
just tested, and the tag of the member when one is left. -/
def otherOf (u : UnionInfo) (ref : DeclRef) (rest : List String) : Ty × Option String :=
  match rest with
  | [o] =>
    match u.members.lookup o with
    | some member => (member, some o)
    | none => (.tagged ref rest, none)
  | _ => (.tagged ref rest, none)

/-- `x.kind === 'circle'` or `x.kind !== 'circle'`, with the string on either
side, where `x` is a local of a tagged union whose tag field is `kind` and
which may have the tag here. Or `typeof x === 'string'` and the like, where
`x` is a local of a union of primitive types. -/
def tagTestOf (env : Env) (e : Expr) : Option TagTest := do
  let .binary _ op l r := e.stripParens | none
  unless op == .strictEq || op == .strictNe do none
  let (n, f, t) ← tagSide l r
  let local_ ← env.lookup n
  let .tagged ref tags := local_.type | none
  let u ← env.unions.find? (·.ref == ref)
  let member ← u.members.lookup t
  unless u.field == f && tags.contains t do none
  let (whenOther, other) := otherOf u ref (tags.filter (· != t))
  return { name := n, ref, field := f, tag := t, isEq := op == .strictEq,
           whenTag := member, whenOther, other }

/-- What `switch (x.kind)` tests: the local, its tagged union, the union's
tag field, and the tags that the local may have where the `switch` starts. -/
structure SwitchOn where
  name : String
  ref : DeclRef
  field : String
  union : UnionInfo
  tags : List String

/-- `switch (x.kind)`, where `x` is a local of a tagged union whose tag field
is `kind`. -/
def switchOf (env : Env) (disc : Expr) : Option SwitchOn := do
  let .member _ (.ident _ n) f := disc.stripParens | none
  let local_ ← env.lookup n
  let .tagged ref tags := local_.type | none
  let u ← env.unions.find? (·.ref == ref)
  unless u.field == f do none
  return { name := n, ref, field := f, union := u, tags }

/-- The statements of a clause of a `switch`: those of its block, when it is
one block, as in `case 'a': { … }`. -/
def clauseStatements : List Stmt → List Stmt
  | [.block _ body] => body
  | body => body

/-- Why a clause of a `switch` must end in `return`. -/
def fallthroughReason : String :=
  "every clause of a switch must end in a return, or every clause in a break; Tolean does not translate fallthrough"

/-- The arm for the other members of a test of `name`'s tag tests it again
only as more arms of the same `match`: first, or not at all. -/
def nestsTag (name : String) : IR.Body → Bool
  | .matchTag n .. => n == name
  | b => !b.testsTag name

/-- A bigint literal other than `0n`, such as `2n` or `-(3n)`. -/
def isNonzeroBigintLiteral : Expr → Bool
  | .paren _ inner | .unary _ .neg inner => isNonzeroBigintLiteral inner
  | .bigint _ text => (bigintValue? text).any (· != 0)
  | _ => false

def numberTest? : String → Option IR.NumberTest
  | "isSafeInteger" => some .isSafeInteger
  | "isNaN" => some .isNaN
  | "isFinite" => some .isFinite
  | _ => none

def numberConstant? : String → Option IR.NumberConstant
  | "NaN" => some .nan
  | "Infinity" => some .posInf
  | _ => none

/-- For a value of type `t`, a `Record<K, V>`: the literal union `K`, the
keys, and `V`. The file must declare or import `K`, so that the output can
name its constructors. -/
def recordIndex (c : Ctx) : Ty → Option (DeclRef × List String × Ty)
  | .struct ref => do
    let info ← c.knownStructs.find? (·.ref == ref)
    let key ← info.key
    let _ ← c.enums.find? (·.ref == key)
    let (_, type) ← info.fields.head?
    return (key, info.fields.map (·.1), type)
  | _ => none

/-! ### Expressions -/

/-- The element type of an array literal: the type that the context gives, or
else the one type of its elements. -/
def elementType (s : Span) (expected : Option Ty) (codes : List Code) : TM Ty :=
  match expected with
  | some t => pure t
  | none => do
    let first ← orReject codes.head? s
      "an empty array needs a declared type, such as 'const xs: ReadonlyArray<bigint> = []'"
    orReject (codes.foldl (fun acc c => acc.bind (·.join c.type)) (some first.type)) s
      "the elements of an array must have one type"

/-- `c`, or the constructor of a literal union when `c` is one of its strings
and the other operand has the union's type, as in `status === 'open'`. Both
are the same string in JS. -/
def enumOperand (known : List EnumInfo) (c : Code) (other : Ty) : Code :=
  match c.code, other with
  | .string m, .enum ref =>
    if (known.find? (·.ref == ref)).any (·.members.contains m) then ⟨.enumCase ref m, false, .enum ref⟩
    else c
  | _, _ => c

/-- The code for `op` on the operands `a` and `b`, which the translator has
already translated. `r` is the right operand, which `/` and `%` read. -/
def applyOperator (s : Span) (op : BinOp) (r : Expr) (a b : Code) : TM Code := do
  let bothBigInt := a.type == .bigint && b.type == .bigint
  let bothNumber := a.type == .number && b.type == .number
  let call (op : IR.NumberOp) (x y : Code) (type : Ty) : Code :=
    ⟨.numberOp op x.value y.value, false, type⟩
  let arithmetic (bigintOp : IR.IntOp) (numberOp : IR.NumberOp) : TM Code := do
    if bothNumber then return call numberOp a b .number
    unless bothBigInt do reject s "arithmetic needs two bigints or two numbers"
    return ⟨.intOp bigintOp a.value b.value, false, .bigint⟩
  -- `a > b` is `b < a`, and `a >= b` is `b <= a`.
  let compare (bigintOp : IR.Order) (numberOp : IR.NumberOp) (swap : Bool) : TM Code := do
    if bothNumber then
      return if swap then call numberOp b a .boolean else call numberOp a b .boolean
    unless bothBigInt do reject s "ordering needs two bigints or two numbers"
    return ⟨.order bigintOp a.value b.value, true, .boolean⟩
  let equal (negated : Bool) : TM Code := do
    if bothNumber then
      return if negated then ⟨.numberNe a.value b.value, false, .boolean⟩
        else call .eq a b .boolean
    if a.type.isObject || b.type.isObject || a.type.isNullable || b.type.isNullable then
      reject s ("=== here would compare objects or nullable values; " ++
        "only primitives and null tests are supported")
    unless a.type == b.type && a.type.isEqPrimitive do
      reject s "=== needs two values of the same primitive type"
    return ⟨if negated then .ne a.value b.value else .eq a.value b.value, true, .boolean⟩
  -- bigint `/` truncates toward zero and `%` takes the sign of the dividend:
  -- Lean's `Int.tdiv` and `Int.tmod`. JS throws on a zero divisor, where Lean
  -- gives a value, so the divisor must be a nonzero literal.
  let divide (operation : IR.Division) : TM Code := do
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

/-- The field `name` that `obj?.name` reads from a value of type `t`: whether
the field is optional, and the type of `obj?.name`. -/
def optFieldType (s : Span) (t : Ty) (name : String) : TM (Bool × Ty) := do
  let some ref := (match t with
      | .nullable (.struct ref) | .optional (.struct ref) => some ref
      | _ => none : Option DeclRef)
    | reject s (if t matches .struct _ then
        "the left side of '?.' is never null or undefined here, so '?.' does nothing; use '.'"
      else "'?.' needs a value of an interface type, or null or undefined")
  let ctx : Ctx ← get
  let field? := (ctx.knownStructs.find? fun (i : StructInfo) => i.ref == ref).bind
    fun info => info.fields.lookup name
  match field? with
  | some (.optional v) => return (true, .optional v)
  | some (.literal _) => reject s "a tag field may be read only in a test of its union, such as x.kind === 'circle'"
  | some v =>
    if v.isNullable then
      reject s "'?.' may not read a nullable field, because the value could be null or undefined"
    return (false, .optional v)
  | none => reject s "only fields of interfaces declared in this file, or exported by the files before it, may be read"

/-- `applyOperator`, after a string operand becomes a constructor where the
other operand is of a literal union. -/
def translateOperator (s : Span) (op : BinOp) (r : Expr) (a b : Code) : TM Code := do
  let known := (← get).knownEnums
  applyOperator s op r (enumOperand known a b.type) (enumOperand known b a.type)

mutual

/-- `expected` is the type the context gives, which an object literal needs:
the return type, a declared type, a parameter type or a field type. Where it
is a union of primitive types, a value of one of its members becomes the
member's constructor. -/
def translateExpr (fuel : Nat) (env : Env) (expected : Option Ty) (e : Expr) : TM Code := do
  let fuel + 1 := fuel | tooDeep
  return (← translateExprCore fuel env expected e).into env.unions expected

/-- `translateExpr`, before a value becomes a member of the union that the
context expects. -/
def translateExprCore (fuel : Nat) (env : Env) (expected : Option Ty) (e : Expr) : TM Code := do
  let fuel + 1 := fuel | tooDeep
  match e with
  | .paren _ inner => translateExpr fuel env expected inner
  | .bigint _ text =>
    -- Typed, so Lean never defaults a numeral to `Nat`, where `0 - 1 = 0`.
    let v ← orReject (bigintValue? text) e.span "a bigint literal must be an integer"
    return ⟨.int v, false, .bigint⟩
  | .number s text =>
    let v ← orReject (safeIntegerValue? text) s "a number literal must be a safe integer"
    return ⟨.number v, false, .number⟩
  | .null _ => return ⟨.none, false, .null⟩
  | .bool _ value => return ⟨.bool value, false, .boolean⟩
  | .string s value =>
    -- In the context of a literal union, a string is one of its constructors.
    match expected with
    | some (.enum ref) | some (.nullable (.enum ref)) =>
      let info ← orReject ((← get).knownEnums.find? (·.ref == ref)) s "unknown literal union"
      unless info.members.contains value do
        reject s s!"'{value}' is not one of the strings of {info.name}"
      return ⟨.enumCase ref value, false, .enum ref⟩
    -- The tag field of an object literal of an interface.
    | some (.literal tag) =>
      unless value == tag do reject s s!"the tag here must be '{tag}'"
      return ⟨.tagValue value, false, .literal value⟩
    | _ => return ⟨.string value, false, .string⟩
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
    -- JS skips the rest of a chain after a `?.` that meets null, so
    -- `a?.b.c` is not `(a?.b).c`, and the subset leaves the chain out.
    if obj matches .optMember .. then reject s "a chain after '?.', such as a?.b.c, is not supported"
    let o ← translateExpr fuel env none obj
    let ctx : Ctx ← get
    let field? := match o.type with
      | .struct ref =>
        (ctx.knownStructs.find? fun (i : StructInfo) => i.ref == ref).bind
          fun info => info.fields.lookup name
      | _ => none
    let message := match o.type, field? with
      | .tagged .., _ => "a field of a tagged union may be read only after a test of its tag"
      | _, some (.literal _) =>
        "a tag field may be read only in a test of its union, such as x.kind === 'circle'"
      | _, _ =>
        "only fields of interfaces declared in this file, or exported by the files before it, may be read"
    -- The structure has no tag field, so the output cannot read one.
    let type ← orReject (field?.filter fun t => !(t matches .literal _)) s message
    return ⟨.field o.code (!obj.isIdent) name, false, type⟩
  | .optMember s obj name =>
    let o ← translateExpr fuel env none obj
    let (bind, type) ← optFieldType s o.type name
    return ⟨.ext (.optField name bind) [o.code], false, type⟩
  | .index s obj key =>
    let o ← translateExpr fuel env none obj
    let (keyRef, keys, type) ← orReject (recordIndex (← get) o.type) s
      "only a value of a Record type, such as type T = Record<K, V>, whose key type K this file declares or imports, may be indexed"
    let k ← translateExpr fuel env (some (.enum keyRef)) key
    unless k.type == .enum keyRef do reject key.span "the key must have the key type of the Record"
    return ⟨.ext (.recordGet keyRef keys) [o.code, k.value], false, type⟩
  | .unary s op arg =>
    if op == .neg && arg.isInfinity && !env.has "Infinity" then
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
    | .typeof =>
      reject s ("typeof may only test, in an if, a local of a union of primitive types " ++
        "against one of its members, as in if (typeof x === 'string') where x has a type " ++
        "such as type T = string | bigint; test a nullable value against null first")
    | _ => reject s "unsupported unary operator"
  | .binary s op l r => translateBinary fuel env s op l r
  | .cond s test ifTrue ifFalse =>
    let c ← translateExpr fuel env none test
    unless c.type == .boolean do reject test.span "a condition must be a boolean"
    let a ← translateExpr fuel env expected ifTrue
    let b ← translateExpr fuel env expected ifFalse
    -- A tag field holds the string itself, which the output leaves out, so
    -- it may not be the value of '?:'.
    let message := match a.type.join b.type with
      | some (.literal _) => "a tag field must be its string literal itself, not the value of '?:'"
      | _ => "the branches of '?:' have different types"
    let type ← orReject ((a.type.join b.type).filter fun t => !(t matches .literal _)) s message
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
    TM (List IR.Expr × Ty) := do
  let fuel + 1 := fuel | tooDeep
  let expectedElem := match expected with
    | some (.array t) => some t
    | _ => none
  let codes ← elems.mapM (translateExpr fuel env expectedElem)
  let elem ← elementType s expectedElem codes
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
  let noCallMessage :=
    "calls may name only functions declared earlier in this file, or imported (no recursion)"
  let noCall {A : Type} : TM A := reject s noCallMessage
  let .ident _ name := callee | noCall
  if (name == "isNaN" || name == "isFinite") && !env.functions.any (·.name == name) then
    reject s s!"the global {name} converts its argument to a number; use Number.{name}"
  let fn ← orReject (env.functions.find? (·.name == name)) s noCallMessage
  if env.has name then noCall
  unless fn.params.length == args.length do reject s s!"'{name}' takes {fn.params.length} arguments"
  let values ← (args.zip fn.params).mapM fun (arg, paramType) => do
    let a ← translateExpr fuel env (some paramType) arg
    unless a.type.assignableTo paramType do
      reject arg.span "the argument does not have the parameter's type"
    pure a.value
  return ⟨.call fn.ref values, false, fn.ret⟩

def translateObject (fuel : Nat) (env : Env) (expected : Option Ty) (s : Span) (props : List Property) :
    TM Code := do
  let fuel + 1 := fuel | tooDeep
  let ctx ← get
  let notStructMessage :=
    "an object literal must build an interface declared in this file, or exported by the files before it"
  -- A member of a tagged union: its tag picks the interface, and the
  -- output wraps the structure in the member's constructor.
  if let some (.tagged uref tags) := expected then
    let union ← orReject (ctx.knownUnions.find? (·.ref == uref)) s notStructMessage
    -- A union of primitive types has no tag field, and no object member.
    let field ← orReject union.field s notStructMessage
    let tag ← orReject (tagOfProps field props) s
      s!"an object of {union.name} must set '{field}' to one of its tags"
    unless tags.contains tag do reject s s!"'{tag}' is not a tag of {union.name} here"
    let member ← orReject (union.members.lookup tag) s s!"'{tag}' is not a tag of {union.name}"
    let c ← translateObject fuel env (some member) s props
    return ⟨.inject uref tag c.code, false, .tagged uref tags⟩
  let some (.struct ref) := expected | reject s notStructMessage
  let info ← orReject (ctx.knownStructs.find? (·.ref == ref)) s notStructMessage
  let structName := ref.name
  -- The keys seen so far, and the fields translated so far.
  let (seen, parts) ← props.foldlM (init := (([] : List String), ([] : List (String × IR.Expr))))
    fun (seen, parts) p => do
      let (key, value, span) ← match p with
        | .shorthand ps name => pure (name, Expr.ident ps name, ps)
        | .keyValue ps (.ident key) v =>
          if key == "__proto__" then reject ps "'__proto__: v' sets the prototype of the object, not a field"
          else pure (key, v, ps)
        | .keyValue ps _ _ => reject ps "object literal fields must be plain name: value pairs"
      let fieldType ← orReject (info.fields.lookup key) span s!"'{key}' is not a field of {structName}"
      if seen.contains key then reject span s!"'{key}' is set twice"
      -- An optional field holds a `T` when the literal sets it. A key that
      -- holds `undefined` is not the same JS value as no key, and Lean has
      -- one `none` for both, so the literal must leave the field out instead.
      let v ← translateExpr fuel env (some fieldType.unoptional) value
      unless v.type.assignableTo fieldType.unoptional do reject span s!"'{key}' does not have the field's type"
      pure (seen ++ [key], parts ++ [(key, v.value)])
  for (field, type) in info.fields do
    unless seen.contains field || type matches .optional _ do
      reject s s!"the object lacks the field '{field}'"
  -- A JS object keeps its keys in the order the literal writes them, and the
  -- caller can see that order, through `Object.keys` or `JSON.stringify`. A
  -- Lean structure has no order, so the literal must use the declared one.
  let declared := (info.fields.map (·.1)).filter seen.contains
  unless seen == declared do
    reject s s!"write the fields in the order that {structName} declares them: {", ".intercalate declared}"
  return ⟨.struct parts ref, false, .struct ref⟩

def translateBinary (fuel : Nat) (env : Env) (s : Span) (op : BinOp) (l r : Expr) : TM Code := do
  let fuel + 1 := fuel | tooDeep
  -- `a ?? b`: `a` unless it is `null`. JS evaluates `b` only when `a` is
  -- `null`, and so does the evaluator of the output.
  if op == .coalesce then
    let a ← translateExpr fuel env none l
    let some value := (match a.type with
        | .nullable v | .optional v => some v
        | _ => none : Option Ty)
      | reject l.span "the left side of '??' is never null here, so '??' does nothing; remove it"
    let b ← translateExpr fuel env (some value) r
    if b.type.assignableTo value then return ⟨.coalesce a.value b.value false, false, value⟩
    unless b.type.assignableTo a.type do
      reject r.span "the right side of '??' must have the type of the left side"
    return ⟨.coalesce a.value b.value true, false, a.type⟩
  -- `x === undefined` and `x !== undefined`, on an optional value: a test on
  -- a Lean `Option`, unless a local hides `undefined`. Other uses of
  -- `undefined` reach the general path, which refuses the name.
  if (l.isUndefinedName || r.isUndefinedName) && !env.has "undefined" && (op == .strictEq || op == .strictNe) then
    let o ← translateExpr fuel env none (if l.isUndefinedName then r else l)
    match o.type with
    | .optional _ => return ⟨if op == .strictEq then .isUndefined o.code else .isDefined o.code, false, .boolean⟩
    | _ => reject s "only the value of an optional field can be undefined here"
  -- `x === null` and `x !== null`, or `==` and `!=`: a test on a Lean `Option`.
  if (nullOp? op).isSome && (l.isNull || r.isNull) then
    let other := if l.isNull then r else l
    if other.isNull then reject s "compare null with a value, not with null"
    let isEquality := nullOp? op == some true
    let o ← translateExpr fuel env none other
    match o.type with
    | .nullable _ =>
      return ⟨if isEquality then .isNone o.code else .isSome o.code, false, .boolean⟩
    | _ =>
      -- The type fixes the answer, as after `if (x === null) return …`. The
      -- test then does nothing, and a constant answer would drop the operand,
      -- which the interpreter still evaluates. So the subset refuses it.
      reject s (if o.type matches .optional _ then
          "the value of an optional field is undefined when the object lacks it, not null; compare it with === undefined"
        else "the type fixes the answer of this test with null, so it does nothing; remove it")
  -- `x === null || e` and `x !== null && e`: TypeScript narrows `x` in `e`,
  -- so Lean matches on `x` and binds it to the value inside.
  if let some (name, isNullTest, value) := nullTestOf env l then
    if (op == .or && isNullTest) || (op == .and && !isNullTest) then
      let whenSome ← translateExpr fuel (env.narrow name value) none r
      unless whenSome.type == .boolean do reject r.span s!"'{op.symbol}' needs two booleans"
      return ⟨.matchNull name (.bool (op == .or)) whenSome.value, false, .boolean⟩
  let a ← translateExpr fuel env none l
  let b ← translateExpr fuel env none r
  translateOperator s op r a b

end

/-! ### Statements -/

def assignOps? : AssignOp → Option (IR.IntOp × IR.NumberOp)
  | .add => some (.add, .add)
  | .sub => some (.sub, .sub)
  | .mul => some (.mul, .mul)
  | _ => none

/-- The value `e`, of type `source`, of a local of type `t`, with the type
written out where Lean would infer another: a `T` or `null` where the local
is `T | null`, and an `if` with `none` in one branch. -/
def withType (e : IR.Expr) (t source : Ty) : IR.Expr :=
  if t.isNullable && (source != t || e matches .none || e matches .ite ..) then
    .ascribe e t.lean
  else e

/-- One mutation statement, as the local it changes and its new value. -/
def translateUpdate (env : Env) (s : Span) (e : Expr) : TM (String × IR.Expr) := do
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
    -- `x ??= e` on a local of `T | null`: `x` unless it is `null`, and then
    -- `e`, which JS evaluates only then. `x` keeps its type.
    if op == .coalesce then
      let some { binding := .«let», type := .nullable value, .. } := env.lookup name
        | reject s "'??=' needs a local declared with let, of a type T | null"
      let v ← translateExpr (← fuelLimit) env (some value) right
      unless v.type.assignableTo (.nullable value) do reject s "the value does not have the local's type"
      return (name, .coalesce (.var name) v.value true)
    unless op.isSimple do refuse
    let some { binding := .«let», type, .. } := env.lookup name
      | reject s "only a local declared with let may be assigned"
    let v ← translateExpr (← fuelLimit) env (some type) right
    match assignOps? op with
    | none =>
      unless v.type.assignableTo type do reject s "the value does not have the local's type"
      return (name, withType v.value type v.type)
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
    TM IR.Body := do
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
    | .switchStmt s disc clauses => translateSwitch fuel env s disc clauses rest tail
    | _ => reject stmt.span "unsupported statement"

def translateVariable (fuel : Nat) (env : Env) (s : Span) (d : VarDecl) (rest : List Stmt)
    (tail : Tail) : TM IR.Body := do
  let fuel + 1 := fuel | tooDeep
  if (Stmt.varDecl s d).constAssignedIn rest then
    reject s s!"'{d.name}' is a const, and a later statement assigns it; declare it with let"
  let init ← orReject d.init s "declare one const or let identifier with an initializer"
  -- `const xs: Array<T> = [...]` (or `T[]`) is an owned array, which the
  -- function may push to. Any other array literal is a value.
  let mutableAnnotation := match d.type with
    | some (.ref _ "Array" [_]) | some (.array _ _) => true
    | _ => false
  if init.isArrayLiteral then
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
  return .let d.name (withType code.value type code.type) (← translateStatements fuel env' tail rest)

def translateIf (fuel : Nat) (env : Env) (s : Span) (test : Expr) (thenBranch : Stmt)
    (elseBranch : Option Stmt) (rest : List Stmt) (tail : Tail) : TM IR.Body := do
  let fuel + 1 := fuel | tooDeep
  let thenStatements := blockStatements thenBranch
  let elseStatements := (elseBranch.map blockStatements).getD []
  -- `if (x === null)` and `if (x !== null)`: TypeScript narrows `x` in each
  -- branch, so Lean matches on `x` and binds it to the value.
  let nullTest := nullTestOf env test
  -- `if (x.kind === 'circle')`: TypeScript narrows `x` to the member in one
  -- branch and to the other members in the other, so Lean matches on the
  -- constructor.
  let tagTest := tagTestOf env test
  let (envTrue, envFalse) := match nullTest, tagTest with
    | some (name, true, value), _ => (env.narrow name .null, env.narrow name value)
    | some (name, false, value), _ => (env.narrow name value, env.narrow name .null)
    | none, some t =>
      if t.isEq then (env.narrow t.name t.whenTag, env.narrow t.name t.whenOther)
      else (env.narrow t.name t.whenOther, env.narrow t.name t.whenTag)
    | none, none => (env, env)
  let branch (whenTrue whenFalse : IR.Body) : TM IR.Body := do
    match nullTest, tagTest with
    | none, none =>
      let c ← translateExpr (← fuelLimit) env none test
      unless c.type == .boolean do reject test.span "a condition must be a boolean"
      return .ite c.code whenTrue whenFalse
    | some (name, isNullTest, _), _ =>
      return if isNullTest then .matchNull name whenTrue whenFalse
        else .matchNull name whenFalse whenTrue
    | none, some t =>
      let (whenTag, whenOther) := if t.isEq then (whenTrue, whenFalse) else (whenFalse, whenTrue)
      -- Where more than one member is left, Lean matches the others with a
      -- catch-all. A further test of the local is exhaustive only as more
      -- arms of the same `match`, so it must come first there.
      if t.other.isNone && !(nestsTag t.name whenOther) then
        reject s ("where more than one member of the union is left, a further test of its tag " ++
          "must come right after, as in a chain of 'if (x.kind === 'a') return …'")
      return .matchTag t.name t.ref t.field t.tag t.other whenTag whenOther
  if tail.isRet && alwaysReturns thenStatements then
    if elseBranch.isSome && !rest.isEmpty then
      reject s "code after an if whose branches both return is unreachable"
    let whenTrue ← translateStatements fuel envTrue tail thenStatements
    let whenFalse ← translateStatements fuel envFalse tail (elseStatements ++ rest)
    return (← branch whenTrue whenFalse)
  if (thenStatements ++ elseStatements).any containsJump then
    reject s "a branch that does not always return may not return, break or continue"
  let names := changedNames (thenStatements ++ elseStatements) env
  if names.isEmpty then reject s "an if without a return must change a local"
  let tested := match nullTest, tagTest with
    | some (name, _, _), _ => some name
    | none, some t => some t.name
    | none, none => none
  if let some name := tested then
    if names.contains name then
      reject s "a local that the test narrows may not be assigned in that if"
  let state := Tail.state names
  let whenTrue ← translateStatements fuel envTrue state thenStatements
  let whenFalse ← translateStatements fuel envFalse state elseStatements
  return .letState names (← branch whenTrue whenFalse) (← translateStatements fuel env tail rest)

/-- `switch (x.kind) { … }`, where every clause returns: a `match` on the
member, as a chain of `if (x.kind === 'a') return …` gives. -/
def translateSwitch (fuel : Nat) (env : Env) (s : Span) (disc : Expr)
    (clauses : List (Option Expr × List Stmt)) (rest : List Stmt) (tail : Tail) : TM IR.Body := do
  let fuel + 1 := fuel | tooDeep
  let some sw := switchOf env disc
    | reject disc.span "a switch must test the tag of a local of a tagged union, as 'switch (x.kind)' does"
  if clausesDeclare clauses then
    reject s "a case that declares a local needs braces, as in case 'a': { const n = 1n; return n; }"
  unless 2 ≤ sw.tags.length do reject s "a switch needs at least two members of its union left to test"
  match clauses with
  | (some _, _) :: _ =>
    if tail.isRet && clauses.all (fun c => alwaysReturns (clauseStatements c.2)) then
      translateClauses fuel env s sw sw.tags none clauses rest
    else if clauses.dropLast.any (fun c => !(alwaysReturns (clauseStatements c.2) || endsInBreak c.2)) then
      reject s fallthroughReason
    else
      -- The clauses end in `break` and change locals, as the branches of an
      -- `if` without a return do.
      let names := changedNames (clauses.flatMap (·.2)) env
      if names.isEmpty then reject s "a switch whose clauses do not return must change a local"
      else if names.contains sw.name then
        reject s "the local that a switch tests may not be assigned in its clauses"
      else
        let branch ← translateStateClauses fuel env s sw sw.tags none names clauses
        return .letState names branch (← translateStatements fuel env tail rest)
  | _ => reject s "the first clause of a switch must be a case"

/-- The clauses of a `switch` from one of them on, where the local may have
the tags `tags`, and where an outer `match` has already found that its tag is
`known`. Each case adds an arm to the `match`. Where one member is left, its
arm runs only for its tag, so the case that names it needs no test of its
own. -/
def translateClauses (fuel : Nat) (env : Env) (s : Span) (sw : SwitchOn) (tags : List String)
    (known : Option String) (clauses : List (Option Expr × List Stmt)) (rest : List Stmt) :
    TM IR.Body := do
  let fuel + 1 := fuel | tooDeep
  match clauses with
  | [] =>
    if tags.isEmpty then reject s "code after a switch whose cases cover every member is unreachable"
    else translateStatements fuel env .ret rest
  | [(none, body)] =>
    if !rest.isEmpty then reject s "code after a switch with a default is unreachable"
    else if !alwaysReturns (clauseStatements body) then reject s fallthroughReason
    else translateStatements fuel env .ret (clauseStatements body)
  | (none, _) :: _ :: _ => reject s "the default must be the last clause of a switch"
  | (some test, body) :: more =>
    match test.stripParens with
    | .string _ tag =>
      match sw.union.members.lookup tag with
      | some member =>
        if !tags.contains tag then
          reject test.span s!"an earlier case of the switch already takes '{tag}'"
        else if !alwaysReturns (clauseStatements body) then reject test.span fallthroughReason
        else
          let whenTag ←
            translateStatements fuel (env.narrow sw.name member) .ret (clauseStatements body)
          let others := tags.filter (· != tag)
          if others.isEmpty then
            if known != some tag then
              reject test.span "the member of this case must be the one left after the cases before it"
            else if !more.isEmpty then
              reject s "the cases before this clause cover every member, so it never runs"
            else if !rest.isEmpty then
              reject s "code after a switch whose cases cover every member is unreachable"
            else return whenTag
          else
            -- The type of the local where the tag is none of the cases so
            -- far, and the member left, when only one is.
            let o := otherOf sw.union sw.ref others
            let whenOther ← translateClauses fuel (env.narrow sw.name o.1) s sw others o.2 more rest
            if o.2.isNone && !(nestsTag sw.name whenOther) then
              reject s ("where more than one member of the union is left, a further test of its tag " ++
                "must be the next case of the switch")
            else return .matchTag sw.name sw.ref sw.field tag o.2 whenTag whenOther
      | none => reject test.span s!"'{tag}' is not the tag of a member of the union"
    | _ => reject test.span "a case of a switch on a tag must be a string"

/-- The clauses of a `switch` whose clauses end in `break`, from one of them
on, as `translateClauses` reads them. Each arm ends in the state of `names`,
and the members that no clause takes keep it as it is. -/
def translateStateClauses (fuel : Nat) (env : Env) (s : Span) (sw : SwitchOn) (tags : List String)
    (known : Option String) (names : List String) (clauses : List (Option Expr × List Stmt)) :
    TM IR.Body := do
  let fuel + 1 := fuel | tooDeep
  match clauses with
  | [] =>
    if tags.isEmpty then reject s "the cases of the switch cover every member, so nothing is left"
    else return .state names
  | [(none, body)] => translateStateClause fuel env s names true body
  | (none, _) :: _ :: _ => reject s "the default must be the last clause of a switch"
  | (some test, body) :: more =>
    match test.stripParens with
    | .string _ tag =>
      match sw.union.members.lookup tag with
      | some member =>
        if !tags.contains tag then
          reject test.span s!"an earlier case of the switch already takes '{tag}'"
        else
          let whenTag ←
            translateStateClause fuel (env.narrow sw.name member) test.span names more.isEmpty body
          let others := tags.filter (· != tag)
          if others.isEmpty then
            if known != some tag then
              reject test.span "the member of this case must be the one left after the cases before it"
            else if !more.isEmpty then
              reject s "the cases before this clause cover every member, so it never runs"
            else return whenTag
          else
            let o := otherOf sw.union sw.ref others
            let whenOther ← translateStateClauses fuel (env.narrow sw.name o.1) s sw others o.2 names more
            if o.2.isNone && !(nestsTag sw.name whenOther) then
              reject s ("where more than one member of the union is left, a further test of its tag " ++
                "must be the next case of the switch")
            else return .matchTag sw.name sw.ref sw.field tag o.2 whenTag whenOther
      | none => reject test.span s!"'{tag}' is not the tag of a member of the union"
    | _ => reject test.span "a case of a switch on a tag must be a string"

/-- One clause of a `switch` whose clauses end in `break`: its statements,
which end in the state of `names`. Only the last clause may leave out its
`break`. -/
def translateStateClause (fuel : Nat) (env : Env) (s : Span) (names : List String) (last : Bool)
    (body : List Stmt) : TM IR.Body := do
  let fuel + 1 := fuel | tooDeep
  if !(last || endsInBreak body) then reject s fallthroughReason
  else if anyContainsJump (dropBreak body) then
    reject s "a clause of a switch that ends in break may not return, break or continue before its end"
  else translateStatements fuel env (.state names) (dropBreak body)

def translateForOf (fuel : Nat) (env : Env) (s : Span) (kind : VarKind) (element : String)
    (iterable : Expr) (body : Stmt) (rest : List Stmt) (tail : Tail) : TM IR.Body := do
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
  let info : IR.LoopInfo :=
    { span := s, elem := elemType.lean,
      stateTypes := names.filterMap fun n => (env.lookup n).map (·.type.lean),
      scope := (env.locals.filter fun l => !names.contains l.name).map fun l => (l.name, l.type.lean) }
  return .fold names element bodyOut items.code (← translateStatements fuel env tail rest) info

end

/-! ### Declarations -/

/-- Run `x` for its result, and keep the state from before it. The parts of a
declaration that only read the state, or change only flags of their own, run
this way: its types, its fields and parameters, and a function body. So the
declarations after it start from the state that the declaration itself sets,
and a proof can read that state from here. -/
def isolated {A : Type} (x : TM A) : TM A := do
  let c ← get
  let r ← x
  set c
  return r

def declareTopLevel (s : Span) (name : String) : TM Unit := do
  let ctx ← get
  if ctx.structs.any (·.name == name) || ctx.aliases.any (·.name == name) ||
      ctx.enums.any (·.name == name) || ctx.unions.any (·.name == name) ||
      ctx.functions.any (·.name == name) then
    reject s s!"'{name}' is declared twice"
  -- A declaration of the module hides the global of the same name, and the
  -- subset reads these names as the globals.
  if isGlobalName name then
    reject s s!"'{name}' would hide the global {name}; choose another name"

def translateInterface (s : Span) (exported : Bool) (name : String) (fields : List Field) :
    TM IR.Decl := do
  let name ← checkName s name
  declareTopLevel s name
  let infos ← isolated <| fields.foldlM (init := ([] : List (String × Ty))) fun infos f => do
    unless f.readonly do
      reject f.span "interface fields must be readonly and typed"
    let field ← checkName f.span f.name
    if infos.any (·.1 == field) then reject f.span s!"'{field}' is declared twice"
    -- A field of one string literal type is a tag, which a union reads.
    let type ← match f.type with
      | .literal _ (.string v) =>
        if f.optional then reject f.span "a tag field may not be optional" else pure (Ty.literal v)
      | t => translateType t
    -- `f?: T`: an object may leave the field out, and a read of it then gives
    -- `undefined`. An object without the field would inherit a property of
    -- `Object.prototype` of the same name.
    let type ← if !f.optional then pure type
      else if type.isNullable then reject f.span "an optional field may not also be nullable"
      else if Eval.objectPrototypeNames.contains field then
        reject f.span s!"an optional field may not be named '{field}', because an object without it has Object.prototype.{field}"
      else pure (Ty.optional type)
    pure (infos ++ [(field, type)])
  modify fun c => { c with structs := c.structs ++ [{ file := c.file, name, exported, fields := infos }] }
  return .struct name (infos.map fun (field, type) => (field, type.lean))

/-- The names that Lean declares itself for every inductive type, so a
constructor may not have one. -/
def inductiveReserved : List String :=
  ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "ctorIdx", "toCtorIdx", "ofNat",
   "ctorElim", "ctorElimType"]

/-- A string of a literal union that can name a constructor: a letter, then
letters, digits and `_`, all ASCII. -/
def memberOK (m : String) : Bool :=
  match m.toList with
  | c :: cs => c.isAlpha && cs.all (fun c => c.isAlphanum || c == '_') && !inductiveReserved.contains m
  | [] => false

/-- The first string of a literal union that cannot name a constructor, with
the reason. -/
def badMember (members : List String) : Option String :=
  members.findSome? fun m =>
    if !memberOK m then
      some s!"'{m}' cannot name a Lean constructor; a literal union needs strings such as 'open'"
    else if members.count m > 1 then some s!"'{m}' is in the union twice"
    else none

/-- `type T = 'a' | 'b'`. A value of the type is one of the strings, and the
output gives the type one constructor for each, so a claim can match on it.
In JS and in the interpreter a value is still the string. -/
def translateEnum (s : Span) (exported : Bool) (name : String) (members : List String) :
    TM IR.Decl := do
  match badMember members with
  | some reason => reject s reason
  | none =>
    modify fun c => { c with enums := c.enums ++ [{ file := c.file, name, exported, members }] }
    return .enum name members

/-- The interfaces of a union `A | B` of interfaces that the file declares or
imports, or none when a member is something else. -/
def unionMembers (structs : List StructInfo) : TypeExpr → Option (List StructInfo)
  | .union _ members => members.mapM fun
    | .ref _ n [] => structs.find? (·.name == n)
    | _ => none
  | _ => none

/-- The tag field of interfaces: a field that each of them has, with one
string literal type, and a different one in each. -/
def tagFieldOf (members : List StructInfo) : Option (String × List String) :=
  match members with
  | [] => none
  | first :: _ =>
    first.fields.findSome? fun (f, _) =>
      let tags := members.filterMap fun m =>
        match m.fields.lookup f with
        | some (.literal t) => some t
        | _ => none
      if tags.length == members.length && tags.eraseDups.length == tags.length then some (f, tags)
      else none

/-- A tagged union with the tag field `field`, or none, and the tag and the
type of each member. The output gives the type one constructor for each
member, which holds the member's value, so a claim can match on it. -/
def declareUnion (s : Span) (exported : Bool) (name : String) (field : Option String)
    (members : List (String × Ty)) : TM IR.Decl := do
  match badMember (members.map (·.1)) with
  | some reason => reject s reason
  | none =>
    modify fun c => { c with unions := c.unions ++ [{ file := c.file, name, exported, field, members }] }
    return .tagged name field (members.map fun (tag, type) => (tag, type.lean))

/-- `type T = A | B`, a union of interfaces with a tag field. Each constructor
holds the member's structure. In JS and in the interpreter a value is still
the object, which has the tag. -/
def translateUnion (s : Span) (exported : Bool) (name : String) (members : List StructInfo) :
    TM IR.Decl := do
  match tagFieldOf members with
  | none =>
    reject s ("a union of interfaces needs a tag: a field that each of them has, " ++
      "with a different string literal type, such as kind: 'circle'")
  | some (field, tags) =>
    declareUnion s exported name (some field) (tags.zip (members.map (.struct ·.ref)))

/-- `type T = string | bigint`, a union of primitive types. Each constructor
holds a value of its type, and its tag is what `typeof` gives for that value,
so `typeof x === 'string'` tests it. In JS and in the interpreter a value is
still the primitive value. -/
def translatePrimitiveUnion (s : Span) (exported : Bool) (name : String) (members : List String) :
    TM IR.Decl := do
  if members.contains "bigint" then requireFeature s .bigint
  declareUnion s exported name none (members.filterMap fun k => (primitiveType? k).map (k, ·))

/-- The key type and the value type of `Record<K, V>`, or of
`Readonly<Record<K, V>>`. -/
def recordArgs : TypeExpr → Option (TypeExpr × TypeExpr)
  | .ref _ "Record" [k, v] | .ref _ "Readonly" [.ref _ "Record" [k, v]] => some (k, v)
  | _ => none

/-- `type T = Record<K, V>`, where `K` is a literal union of strings that the
file declares or imports. A value of the type has a property for each string
of `K`, so the output declares a structure with one field of type `V` for
each, in the order of `K`. An object literal must set every key in that
order, as for an interface. `r[k]` reads the field that `k` names. -/
def translateRecord (exported : Bool) (name : String) (key value : TypeExpr) :
    TM IR.Decl := do
  let keyType ← isolated (translateType key)
  let ctx ← get
  let info ← orReject (match keyType with
      | .enum ref => ctx.enums.find? (·.ref == ref)
      | _ => none) key.span
    "the keys of a Record must be a literal union of strings that this file declares or imports, such as type K = 'a' | 'b'"
  let type ← isolated (translateType value)
  if let some m := info.members.find? leanReserved.contains then
    reject key.span s!"name '{m}' is reserved in Lean, so it cannot name a field of the Record"
  let fields := info.members.map fun m => (m, type)
  modify fun c =>
    { c with structs := c.structs ++ [{ file := c.file, name, exported, fields, key := some info.ref }] }
  return .struct name (fields.map fun (field, type) => (field, type.lean))

/-- `type T = U`. The translator writes the type of `U` wherever the source
names `T`, so a type alias changes no code. The output declares it as an
`abbrev`, for the claims about the code to use. An alias must come before its
uses, as an interface must. -/
def translateAlias (s : Span) (exported : Bool) (name : String) (type : TypeExpr) :
    TM IR.Decl := do
  let name ← checkName s name
  declareTopLevel s name
  if let some members := stringLiterals type then
    return ← translateEnum s exported name members
  if let some members := unionMembers (← get).structs type then
    return ← translateUnion s exported name members
  if let some members := primitiveMembers type then
    return ← translatePrimitiveUnion s exported name members
  if let some (key, value) := recordArgs type then
    return ← translateRecord exported name key value
  let ty ← isolated (translateType type)
  modify fun c => { c with aliases := c.aliases ++ [{ file := c.file, name, exported, type := ty }] }
  return .alias name ty.lean

def translateFunction (s : Span) (exported : Bool) (name : String) (params : List Param)
    (returnType : Option TypeExpr) (body : Stmt) : TM IR.Decl := do
  let some returnType := returnType
    | reject s "functions must be named, typed, non-generic and synchronous"
  let name ← checkName s name
  declareTopLevel s name
  -- The scope of the body, and the parameters in Lean and as types.
  let (env, leanParams, types) ← isolated <| params.foldlM
    (init := (({ functions := (← get).functions, unions := (← get).knownUnions } : Env), ([] : List (String × IR.Ty)), ([] : List Ty)))
    fun (env, leanParams, types) p => do
      let type ← orReject p.type p.span "parameters must be plain, typed identifiers"
      let paramName ← checkLocalName p.span p.name
      if env.has paramName then reject p.span s!"'{paramName}' is declared twice"
      let ty ← translateType type
      pure (env.add { name := paramName, binding := .param, type := ty },
        leanParams ++ [(paramName, ty.lean)], types ++ [ty])
  let ret ← isolated (translateType returnType)
  modify fun c => { c with currentFunction := name, returnType := ret }
  let out ← isolated (translateStatements (← fuelLimit) env .ret (blockStatements body))
  modify fun c => { c with functions := c.functions ++ [{ file := c.file, name, exported, params := types, ret }] }
  return .function name leanParams ret.lean out

/-! ### The number model -/

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
  | .member _ obj name | .optMember _ obj name => isNumberName name || exprUsesNumber obj
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
    -- An import of one of these names is refused, so an import adds nothing.
    | .import .. => false
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

/-- `import { a, type B } from "./x.ts"`. Each name becomes a function or an
interface of the file, as the file it names exports it. That file must be
translated first. -/
def translateImport (s : Span) (names : List ImportName) (source : String) : TM Unit := do
  let ctx ← get
  let target ← orReject (Eval.resolvePath ctx.file source) s
    s!"'{source}' is not a relative path to a .ts file, such as './x.ts'"
  let iface ← orReject (ctx.interfaces.lookup target) s
    (s!"'{source}' is not a translated file of the project: an import needs a tolean.json " ++
      "project, and the file it imports from must be among its sources and translate")
  if ctx.target.year < iface.target.year then
    reject s (s!"'{source}' is translated for {iface.target.name}, which is newer than this " ++
      s!"file's {ctx.target.name}")
  names.forM fun n => do
    declareTopLevel n.span n.name
    if n.typeOnly then
      match iface.aliases.find? (·.name == n.name),
          iface.enums.find? fun e => e.name == n.name && e.exported with
      | some info, _ =>
        modify fun c => { c with aliases := c.aliases ++ [{ info with exported := false }] }
      | none, some info =>
        modify fun c => { c with enums := c.enums ++ [{ info with exported := false }] }
      | none, none =>
      match iface.unions.find? fun u => u.name == n.name && u.exported with
      | some info =>
        modify fun c => { c with unions := c.unions ++ [{ info with exported := false }] }
      | none =>
        let info ← orReject (iface.structs.find? fun i => i.name == n.name && i.exported) n.span
          s!"'{source}' exports no interface or type named '{n.name}'"
        modify fun c => { c with structs := c.structs ++ [{ info with exported := false }] }
    else
      if iface.structs.any fun i => i.name == n.name && i.exported then
        reject n.span s!"'{n.name}' is an interface; import it with 'type {n.name}'"
      if iface.aliases.any (·.name == n.name) || (iface.enums.any fun e => e.name == n.name && e.exported) ||
          iface.unions.any fun u => u.name == n.name && u.exported then
        reject n.span s!"'{n.name}' is a type; import it with 'type {n.name}'"
      let fn ← orReject (iface.functions.find? (·.name == n.name)) n.span
        s!"'{source}' exports no function named '{n.name}'"
      modify fun c => { c with functions := c.functions ++ [{ fn with exported := false }] }

/-- One declaration: an output declaration, or none for an import. -/
def translateDecl : Decl → TM (Option IR.Decl)
  | .import s names source => do translateImport s names source; return none
  | .interface s exported name fields => some <$> translateInterface s exported name fields
  | .typeAlias s exported name type => some <$> translateAlias s exported name type
  | .function s exported name params ret body =>
    some <$> translateFunction s exported name params ret body
  | d => reject d.span "only imports, interfaces, types and functions may appear at top level"

/-- The declarations of `m`, translated. This is the translator as a function
from one syntax tree to another: `translate` parses the source before it and
prints the result after it. -/
def translateDecls (m : Module) : TM (List IR.Decl) := do
  return (← m.decls.mapM translateDecl).filterMap id

/-- The declarations that a type names: interfaces, literal unions and
tagged unions. -/
def Ty.declRefs : Ty → List DeclRef
  | .struct r | .enum r | .tagged r _ => [r]
  | .nullable t | .optional t | .array t => t.declRefs
  | _ => []

/-- The file's own types that a file importing from it needs: the exported
ones, and the private ones that an exported alias, interface, union or
function names, directly or through the fields of an interface or the
members of a union. A type names only the ones before it, so as many rounds
as the file has types find them all. -/
def Ctx.reachable (c : Ctx) : List DeclRef :=
  let own := c.structs.filter (·.file == c.file)
  let ownUnions := c.unions.filter (·.file == c.file)
  let roots := (c.aliases.filter fun a => a.exported && a.file == c.file).flatMap (·.type.declRefs) ++
    (own.filter (·.exported)).map (·.ref) ++
    (c.enums.filter fun e => e.exported && e.file == c.file).map (·.ref) ++
    (ownUnions.filter (·.exported)).map (·.ref) ++
    (c.functions.filter fun f => f.exported && f.file == c.file).flatMap
      fun f => (f.ret :: f.params).flatMap (·.declRefs)
  let step (seen : List DeclRef) : List DeclRef :=
    seen ++ (own.filter fun i => seen.contains i.ref).flatMap (·.fields.flatMap (·.2.declRefs)) ++
      (ownUnions.filter fun u => seen.contains u.ref).flatMap (·.members.flatMap (·.2.declRefs))
  (List.range (own.length + ownUnions.length)).foldl (fun acc _ => step acc) roots

/-- The file's interfaces that a file importing from it needs the fields of.
The private ones keep `exported := false`, so no file can import them by
name. -/
def Ctx.reachableStructs (c : Ctx) : List StructInfo :=
  let reached := c.reachable
  c.structs.filter fun i => i.file == c.file && (i.exported || reached.contains i.ref)

/-- The file's literal unions that a file importing from it needs the strings
of. -/
def Ctx.reachableEnums (c : Ctx) : List EnumInfo :=
  let reached := c.reachable
  c.enums.filter fun e => e.file == c.file && (e.exported || reached.contains e.ref)

/-- The file's tagged unions that a file importing from it needs the members
of. -/
def Ctx.reachableUnions (c : Ctx) : List UnionInfo :=
  let reached := c.reachable
  c.unions.filter fun u => u.file == c.file && (u.exported || reached.contains u.ref)

/-- What the file exports: its own exported functions, interfaces and type
aliases. The interfaces include the private ones that an exported declaration
names, so that a file that imports it can read and build their fields. They
keep `exported := false`, so that no file can import them by name. -/
def Ctx.interface (c : Ctx) (usesNumber : Bool) (numberVar : String) : Interface :=
  { functions := c.functions.filter fun f => f.exported && f.file == c.file,
    structs := c.reachableStructs,
    aliases := c.aliases.filter fun a => a.exported && a.file == c.file,
    enums := c.reachableEnums,
    unions := c.reachableUnions,
    usesNumber, numberVar, target := c.target }

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

/-- Another file of the project, as the translation of a file that imports
from it needs it: the Lean module and the namespace of its translation, and
what it exports. -/
structure Dependency where
  module : String
  ns : String
  interface : Interface
  /-- The files that it imports from, and the files that those import from. -/
  imports : List String := []

/-- The files that `m`, the module of `file`, imports from, in the order of its
imports, without repeats. -/
def importedFiles (file : String) (m : Module) : List String :=
  (m.decls.filterMap fun
    | .import _ _ source => Eval.resolvePath file source
    | _ => none).eraseDups

/-- Parse and translate `source`, the TypeScript file `file`, which may import
from the files `deps`: the parsed module, the names that the printer needs,
the Tolean IR, and what the file exports. -/
def translateFile (file source : String) (target : Edition := .default)
    (deps : List (String × Dependency) := []) :
    Except String (Module × IR.Names × List IR.Decl × Interface) := do
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
  let imported := (importedFiles file m).filterMap fun f => (deps.lookup f).map (f, ·)
  -- A file that imports from a generic file is generic too, so that it has a
  -- number type to pass.
  let usesNumber := moduleUsesNumber m || imported.any (·.2.interface.usesNumber)
  let names : IR.Names :=
    { clashes := IR.leanNames.map (·.1) |>.filter idents.contains,
      typeParam := numberVar.getD "N", generic := usesNumber, file,
      -- Every file before this one, not only the ones it imports: a type can
      -- reach it through the field types of an imported interface.
      imported := deps.map fun (f, d) =>
        (f, { ns := d.ns, generic := d.interface.usesNumber, typeParam := d.interface.numberVar }) }
  let ctx : Ctx :=
    { file, target, src, lineStarts := lineStarts src, fuel := 4 * src.size + 4,
      interfaces := deps.map fun (f, d) => (f, d.interface) }
  match (translateDecls m).run ctx with
  | .error e _ => .error e
  | .ok decls ctx' => return (m, names, decls, ctx'.interface usesNumber names.typeParam)

/-- Parse and translate `source`, the TypeScript file `file`: the parsed
module, the names that the printer needs, and the Tolean IR. -/
def translateTree (file source : String) (target : Edition := .default) :
    Except String (Module × IR.Names × List IR.Decl) := do
  let (m, names, decls, _) ← translateFile file source target
  return (m, names, decls)

/-- A TypeScript file, translated to a Lean file. -/
structure Translated where
  lean : String
  /-- What the file exports. -/
  interface : Interface
  /-- The files that it imports from, and the files that those import from.
  Its meaning depends on them all. -/
  imports : List String

/-- Translate `source`, the TypeScript file `file`, to a Lean file whose
definitions are in namespace `ns`, for code that runs on the edition
`target`. `deps` are the files it may import from. -/
def translateWith (file source ns : String) (target : Edition := .default)
    (deps : List (String × Dependency) := []) : Except String Translated := do
  let (m, names, decls, iface) ← translateFile file source target deps
  -- Inside `namespace A.B`, Lean finds a plain name in `A.B` and `A` first.
  -- So a file whose namespace is, or holds, another file's would let that
  -- file's declarations capture the plain names that the output writes, such
  -- as `decide`, and two files with one namespace collide outright.
  let inside (a b : String) : Bool := a == b || a.startsWith (b ++ ".")
  if let some (f, d) := deps.find? fun (_, d) => inside ns d.ns || inside d.ns ns then
    throw s!"{file}: its namespace {ns} and the namespace {d.ns} of {f} nest; set namespace for one of them"
  -- The printer writes a declaration of another file with that file's
  -- namespace, so it must know the file. The translator only names files it
  -- sees, and this check keeps a later change from printing a bare name.
  if let some r := (decls.flatMap IR.Decl.refs).find? fun r =>
      r.file != file && (deps.lookup r.file).isNone then
    throw s!"{file}: the output names '{r.name}' of '{r.file}', a file that it does not see"
  let imports := (importedFiles file m).filterMap fun f => (deps.lookup f).map (s!"import {·.module}")
  let header :=
    (if names.generic then ["import tolean.TypeScript.Spec.Number"] else []) ++ imports ++
    (if names.generic then ["", "open tolean.TypeScript"] else if imports.isEmpty then [] else [""])
  let text := "\n".intercalate
    ([s!"-- Generated by tolean {version} for {target.name} from {file}. Do not edit."] ++
      header ++
      [s!"namespace {ns}", "", "\n\n".intercalate (decls.map (·.print names)), "", s!"end {ns}", ""])
  let chain := (importedFiles file m).flatMap fun f => f :: ((deps.lookup f).map (·.imports)).getD []
  return { lean := text, interface := iface, imports := chain.eraseDups }

/-- Translate `source`, the TypeScript file `file`, to a Lean file whose
definitions are in namespace `ns`, for code that runs on the edition
`target`. -/
def translate (file source ns : String) (target : Edition := .default) :
    Except String String :=
  (·.lean) <$> translateWith file source ns target

end tolean.TypeScript.Translate
