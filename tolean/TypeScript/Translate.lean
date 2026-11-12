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
  imports. `args` are the types of a generic interface's type parameters. -/
  | struct (ref : DeclRef) (args : List Ty)
  /-- A literal union of strings, `type T = 'a' | 'b'`, of the program. -/
  | enum (ref : DeclRef)
  /-- A tagged union of interfaces of the program, `type T = A | B`, narrowed
  to the members with the tags `tags`. -/
  | tagged (ref : DeclRef) (tags : List String)
  /-- The type of a tag field, one string literal such as `'circle'`. -/
  | literal (value : String)
  /-- A tuple `[A, B]` of two elements or more. -/
  | tuple (elems : List Ty)
  /-- A type parameter of a generic function, such as `T` in
  `function first<T>(xs: T[]): T | null`. -/
  | param (name : String)
  /-- `Map<K, V>` or `ReadonlyMap<K, V>`, where `K` is a bigint, a string, a
  boolean or a literal union of strings. -/
  | map (key value : Ty)
  /-- `Set<T>` or `ReadonlySet<T>`, where `T` is a type that a map key may
  have. -/
  | set (elem : Ty)
deriving Repr, Inhabited

-- `Ty` holds lists of itself, so Lean's derived `BEq` would not reduce in the
-- kernel, which runs the translator for a certificate. These recurse on the
-- type instead.
mutual

def Ty.beq : Ty → Ty → Bool
  | .bigint, .bigint | .number, .number | .boolean, .boolean | .string, .string | .null, .null => true
  | .nullable a, .nullable b | .optional a, .optional b | .array a, .array b => Ty.beq a b
  | .struct a as, .struct b bs => a == b && Ty.beqList as bs
  | .enum a, .enum b => a == b
  | .tagged a ts, .tagged b us => a == b && ts == us
  | .literal a, .literal b => a == b
  | .tuple as, .tuple bs => Ty.beqList as bs
  | .param a, .param b => a == b
  | .map a a', .map b b' => Ty.beq a b && Ty.beq a' b'
  | .set a, .set b => Ty.beq a b
  | _, _ => false

def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false

end

instance : BEq Ty := ⟨Ty.beq⟩

mutual

/-- A value of type `source` has the Lean type of `target` as it is: the same
type, `null` where `T | null` is expected, a union narrowed to some of its
members, or a tuple of such elements. A `T` where `T | null` is expected is
not one: Lean converts a value to `Option T`, but not each element of a pair.
-/
def Ty.sameLean (source target : Ty) : Bool :=
  source == target ||
    match target, source with
    | .nullable _, .null => true
    | .tagged ref tags, .tagged ref' tags' => ref' == ref && tags'.all tags.contains
    | .tuple ts, .tuple ss => Ty.sameLeanList ss ts
    | _, _ => false

def Ty.sameLeanList : List Ty → List Ty → Bool
  | [], [] => true
  | s :: ss, t :: ts => s.sameLean t && Ty.sameLeanList ss ts
  | _, _ => false

end

/-- A value of type `source` can stand where `target` is expected. Arrays and
structures must match exactly. A tuple can stand where each of its elements
has the Lean type of its place: `[null, x]` is a `[T | null, T]`, but a tuple
of type `[T, T]` is not. -/
def Ty.assignableTo (source target : Ty) : Bool :=
  source.sameLean target ||
    match target with
    | .nullable value => source == value
    | _ => false

/-- A value of type `source` can be the argument of a parameter of type
`param`. An optional parameter takes a `T` too, which Lean coerces to
`some`. -/
def Ty.passableTo (source param : Ty) : Bool :=
  source.assignableTo param ||
    match param with
    | .optional t => source.assignableTo t
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

/-- The spread that an object literal starts with, and the properties after
it. -/
def spreadOf : List Property → Option (Expr × List Property)
  | .spread _ base :: rest => some (base, rest)
  | _ => none

/-- The operand of a spread `...e`. -/
def _root_.tolean.TypeScript.Syntax.Expr.spreadArg? : Expr → Option (Span × Expr)
  | .spread sp e => some (sp, e)
  | _ => none

/-- The interface of a value of an interface type, with its type arguments. -/
def Ty.structRef? : Ty → Option (DeclRef × List Ty)
  | .struct ref args => some (ref, args)
  | _ => none

/-- An optional field, or a tag field, which a property after a spread may
not set. -/
def Ty.isMaybeField : Ty → Bool
  | .optional _ | .literal _ => true
  | _ => false

/-- The type of a tag field, one string literal. -/
def Ty.isLiteral : Ty → Bool
  | .literal _ => true
  | _ => false

/-- `T | null`. -/
def Ty.isNullable : Ty → Bool
  | .nullable _ => true
  | _ => false

/-- `null`, `T | null` or an optional value: a type whose values the output
writes with `none`. -/
def Ty.isMaybe : Ty → Bool
  | .null | .nullable _ | .optional _ => true
  | _ => false

/-- The value of an optional field `f?: T`. -/
def Ty.isOptional : Ty → Bool
  | .optional _ => true
  | _ => false

/-- A primitive that `===` compares by value and the output compares with `=`. -/
def Ty.isEqPrimitive : Ty → Bool
  | .boolean | .string | .bigint | .enum _ => true
  | _ => false

/-- An object, which `===` compares by identity. A tuple is an array. -/
def Ty.isObject : Ty → Bool
  | .array _ | .struct .. | .tagged .. | .tuple _ | .map .. | .set _ => true
  | _ => false

/-- The element types of a tuple type. -/
def Ty.tupleElems? : Ty → Option (List Ty)
  | .tuple ts => some ts
  | _ => none

/-- What `typeof` gives for a value of type `t`, when `t` is a primitive type
that a union of primitive types may have as a member. -/
def Ty.typeOf? : Ty → Option String
  | .bigint => some "bigint"
  | .number => some "number"
  | .boolean => some "boolean"
  | .string => some "string"
  | _ => none

mutual

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
  | .struct ref [] => .struct ref
  | .struct ref (a :: as) => .app ref (Ty.leanList (a :: as))
  | .enum ref => .enum ref
  | .tagged ref _ => .tagged ref
  | .literal value => .tag value
  | .tuple ts => .tuple (Ty.leanList ts)
  | .param name => .param name
  | .map k v => .map k.lean v.lean
  | .set t => .set t.lean

def Ty.leanList : List Ty → List IR.Ty
  | [] => []
  | t :: ts => t.lean :: Ty.leanList ts

end

/-- `t` names a type parameter. -/
def Ty.isGeneric (t : Ty) : Bool := !t.lean.typeVars.isEmpty

/-- The type that the context expects of a value where `t` is expected, while
the type parameters that `t` names are not fixed yet: `t` itself when it names
none, and a tuple's shape, so that an array literal is still read as a tuple.
Each element of the tuple is then read on its own terms. -/
def Ty.callExpected (t : Ty) : Option Ty :=
  if !t.isGeneric then some t
  else if t matches .tuple _ then some t
  else none

/-- A type that a type parameter may stand for. `T | null` stands for one
Lean type, `Option T`, so `T` may not be nullable itself: `Option (Option U)`
has two values where JS has one `null`. A tag literal is not a type of its
own in the output. -/
def Ty.bindable : Ty → Bool
  | .null | .nullable _ | .optional _ | .literal _ => false
  | _ => true

mutual

/-- `t` with each type parameter that `sol` gives a type replaced by it. -/
def Ty.subst (sol : List (String × Ty)) : Ty → Ty
  | .param name => (sol.lookup name).getD (.param name)
  | .nullable t => .nullable (t.subst sol)
  | .optional t => .optional (t.subst sol)
  | .array t => .array (t.subst sol)
  | .tuple ts => .tuple (Ty.substList sol ts)
  | .struct ref args => .struct ref (Ty.substList sol args)
  | .map k v => .map (k.subst sol) (v.subst sol)
  | .set t => .set (t.subst sol)
  | t => t

def Ty.substList (sol : List (String × Ty)) : List Ty → List Ty
  | [] => []
  | t :: ts => t.subst sol :: Ty.substList sol ts

end

mutual

/-- `sol`, the types found so far for the type parameters of a call, with the
ones that an argument of type `t` gives for a parameter of type `pattern`. A
parameter of type `T | null` takes `null` without fixing `T`. -/
def Ty.unify (sol : List (String × Ty)) : Ty → Ty → List (String × Ty)
  | .param name, t => if (sol.lookup name).isNone && t.bindable then sol ++ [(name, t)] else sol
  | .nullable p, .nullable t => Ty.unify sol p t
  | .nullable p, t => Ty.unify sol p t
  | .optional p, .optional t => Ty.unify sol p t
  -- An optional parameter takes a value of its type too, which fixes the type
  -- parameters as the type would.
  | .optional p, t => Ty.unify sol p t
  | .array p, .array t => Ty.unify sol p t
  | .tuple ps, .tuple ts | .struct _ ps, .struct _ ts => Ty.unifyList sol ps ts
  | .map pk pv, .map tk tv => Ty.unify (Ty.unify sol pk tk) pv tv
  | .set p, .set t => Ty.unify sol p t
  | _, _ => sol

def Ty.unifyList (sol : List (String × Ty)) : List Ty → List Ty → List (String × Ty)
  | p :: ps, t :: ts => Ty.unifyList (Ty.unify sol p t) ps ts
  | _, _ => sol

end

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

/-- How a name in scope may be used. Only `let`, `array` and `map` locals
change. An `array` or a `map` local is owned: the function made it, and
nothing else holds it. A `map` local holds a map or a set. -/
inductive Binding where
  | param | const | «let» | array | map
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
  /-- The type parameters of a generic interface, which its field types name. -/
  typeParams : List String := []
  fields : List (String × Ty)
  /-- For `type T = Record<K, V>`, the literal union `K`, whose strings are
  the fields. An index `r[k]` with a key of type `K` reads one. -/
  key : Option DeclRef := none

def StructInfo.ref (i : StructInfo) : DeclRef := ⟨i.file, i.name⟩

/-- The fields of the interface where its type parameters are `args`. -/
def StructInfo.fieldsAt (i : StructInfo) (args : List Ty) : List (String × Ty) :=
  i.fields.map fun (f, t) => (f, t.subst (i.typeParams.zip args))

/-- A function of the program, with the file that declares it. -/
structure FnInfo where
  file : String
  name : String
  exported : Bool := false
  /-- The type parameters of a generic function, which its parameter types
  and its result type name. -/
  typeParams : List String := []
  params : List Ty
  ret : Ty
  /-- The function can throw, so its output returns `Except JSError R`. -/
  throws : Bool := false

def FnInfo.ref (f : FnInfo) : DeclRef := ⟨f.file, f.name⟩

/-- A string enum whose members code may read, such as `Color.Red`: its
name in the file, its declaration, and the name and the string of each
member. -/
structure EnumValue where
  name : String
  ref : DeclRef
  members : List (String × String)

/-- The names in scope, in the order they were declared, and the functions
that a call may name. -/
structure Env where
  locals : List Local := []
  functions : List FnInfo := []
  /-- The tagged unions whose tags a test may read. -/
  unions : List UnionInfo := []
  /-- The string enums whose members code may read: the file's own, and the
  ones it imports without `type`. -/
  enums : List EnumValue := []

def Env.lookup (env : Env) (name : String) : Option Local := env.locals.find? (·.name == name)

def Env.has (env : Env) (name : String) : Bool := (env.lookup name).isSome

def Env.add (env : Env) (l : Local) : Env := { env with locals := env.locals ++ [l] }

/-- `name` has the type `type` from here on, as after `x !== null`. -/
def Env.narrow (env : Env) (name : String) (type : Ty) : Env :=
  { env with locals := env.locals.map fun l => if l.name == name then { l with type } else l }

/-- A literal union of strings of the program, `type T = 'a' | 'b'`, with the
file that declares it and its strings in the order of the source. A string
enum, `enum T { A = 'a', B = 'b' }`, is one too, with the name and the
string of each member in `named`. -/
structure EnumInfo where
  file : String
  name : String
  exported : Bool := false
  members : List String
  named : Option (List (String × String)) := none

def EnumInfo.ref (i : EnumInfo) : DeclRef := ⟨i.file, i.name⟩

/-- A type alias of the program, `type T = U`, with the file that declares
it. `type` is the type of `U`, which the translator writes wherever the
source names `T`. -/
structure AliasInfo where
  file : String
  name : String
  exported : Bool := false
  /-- The type parameters of a generic alias, which `type` may name. -/
  typeParams : List String := []
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
  /-- The string enums whose members the file's code may read. -/
  enumValues : List EnumValue := []
  /-- The files that this file may import from, by path. -/
  interfaces : List (String × Interface) := []
  currentFunction : String := ""
  /-- The type parameters of the function being translated. -/
  typeParams : List String := []
  returnType : Ty := .boolean
  /-- The function being translated can throw, so its output returns
  `Except JSError R`, and each value it returns is `pure` of the value. -/
  throws : Bool := false
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

/-- An `undefined` argument whose type names type parameters of the function
that it is passed to, which the other arguments have to fix. -/
def Code.unfixed (c : Code) : Bool := c.value matches .undefined && c.type.isGeneric

/-- The type parameters of a function that the arguments of a call other than
its `undefined` ones fix. A type parameter may be fixed to a type that names
the caller's own type parameters. -/
def fixedParams (params : List Ty) (first : List Code) : List (String × Ty) :=
  let fixing := params.zip first |>.filter fun (_, c) => !c.unfixed
  Ty.unifyList [] (fixing.map (·.1)) (fixing.map (·.2.type))

/-- An `undefined` argument whose type names a type parameter that the other
arguments do not fix. -/
def Code.unfixedBy (known : List (String × Ty)) (c : Code) : Bool :=
  c.unfixed && !(c.type.lean.typeVars.all fun v => (known.lookup v).isSome)

/-- The arguments of a call, where each `undefined` argument for a generic
optional parameter gets that parameter's type with the type parameters that
the other arguments fix. -/
def fixArgs (params : List Ty) (first : List Code) : List Code :=
  let known := fixedParams params first
  first.map fun c => if c.unfixed then { c with type := c.type.subst known } else c

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

mutual

/-- A value of type `a` has the type `t`, where a value of a member of a union
of primitive types counts as a value of the union, inside arrays, tuples and
nullable types too. This is how TypeScript checks `satisfies`; the value
keeps the type `a`. -/
def Ty.fits (unions : List UnionInfo) : Ty → Ty → Bool
  | a, .tagged ref tags => a.assignableTo (.tagged ref tags) ||
    a.typeOf?.any fun k => (unions.any fun u => u.ref == ref && u.field.isNone) && tags.contains k
  | a, .nullable t => a.assignableTo (.nullable t) || a == .null ||
    match a with
    | .nullable a' => Ty.fits unions a' t
    | _ => Ty.fits unions a t
  | a, .array t => a.assignableTo (.array t) ||
    match a with
    | .array a' => Ty.fits unions a' t
    | _ => false
  | a, .tuple ts => a.assignableTo (.tuple ts) ||
    match a with
    | .tuple as => Ty.fitsList unions as ts
    | _ => false
  | a, t => a.assignableTo t

/-- Each type of `as` fits the type of `ts` at its place. -/
def Ty.fitsList (unions : List UnionInfo) : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, t :: ts => Ty.fits unions a t && Ty.fitsList unions as ts
  | _, _ => false

end

/-- What a statement list ends in: a `return`, or the tuple of changed locals. -/
inductive Tail where
  | ret
  /-- The end of a branch, or of a clause of a `switch`. -/
  | state (names : List String)
  /-- The end of a loop body, which a `continue` also reaches. `breaks` says
  whether a `break` or a `return` can end the loop, so that each run of the
  body gives a `ForInStep`. `returns` says whether a `return` can, so that
  the state starts with the value to return. -/
  | loop (names : List String) (breaks returns : Bool)
  /-- A `continue`, a `break` or a `return`, which every path must reach: the
  statements are a branch that ends one run of a loop body. -/
  | cont (names : List String) (breaks returns : Bool)

def Tail.isRet : Tail → Bool
  | .ret => true
  | _ => false

/-- The end of one run of a loop body with the locals `names`: their tuple,
or `ForInStep.yield` of it in a loop that a `break` or a `return` can end. -/
def stepEnd (names : List String) (breaks returns : Bool) : IR.Body :=
  if breaks then .yield names returns else .state names

/-- The end of one run of a loop body, where a `continue` may end the
statements. -/
def Tail.continues : Tail → Option IR.Body
  | .loop names b r | .cont names b r => some (stepEnd names b r)
  | _ => none

/-- The end of a loop, where a `break` may end the statements. -/
def Tail.breaks : Tail → Option IR.Body
  | .loop names true r | .cont names true r => some (.done names r)
  | _ => none

/-- A `return` may end the statements: they are a function body, or the body
of a loop that a `return` can end. -/
def Tail.canReturn : Tail → Bool
  | .ret => true
  | .loop _ _ r | .cont _ _ r => r
  | .state _ => false

/-- What a `return` of `code` gives: the function's value, or in a loop body,
the end of the loop with the value to return. -/
def Tail.returnBody (tail : Tail) (code : IR.Expr) : IR.Body :=
  match tail with
  | .loop names _ _ | .cont names _ _ => .exit code names
  | _ => .value code

def leanReserved : List String := IR.leanReserved

/-- The type of the output of a function whose result has the type `ret`:
`Except JSError R` when it can throw. -/
def leanResult (throws : Bool) (ret : Ty) : IR.Ty :=
  if throws then .except IR.Ty.error ret.lean else ret.lean

/-- The parts of `e` when it is a call of a function of `fns` that can
throw: the spans of the call and of the name, the name, and the arguments. -/
def throwingCall? (fns : List FnInfo) : Expr → Option (Span × Span × String × List Expr)
  | .call cs (.ident sp name) args =>
    if (fns.find? (·.name == name)).any (·.throws) then some (cs, sp, name, args) else none
  | _ => none

/-- `e` is a call of a function of `fns` that can throw. -/
def callsThrowing (fns : List FnInfo) (e : Expr) : Bool := (throwingCall? fns e).isSome

mutual

/-- `s` can throw: it holds a `throw`, or a declaration or a `return` whose
value is a call of a function of `fns` that can throw. -/
def stmtThrows (fns : List FnInfo) : Stmt → Bool
  | .throwStmt .. => true
  | .varDecl _ { init := some e, .. } | .returnStmt _ (some e) => callsThrowing fns e
  | .ifStmt _ _ t (some e) => stmtThrows fns t || stmtThrows fns e
  | .ifStmt _ _ t none => stmtThrows fns t
  | .forOfStmt _ _ _ _ body | .forOfPattern _ _ _ _ body | .forStmt _ _ _ _ body | .whileStmt _ _ body =>
    stmtThrows fns body
  | .block _ body => stmtsThrow fns body
  | .switchStmt _ _ clauses => clausesThrow fns clauses
  | _ => false

def stmtsThrow (fns : List FnInfo) : List Stmt → Bool
  | [] => false
  | s :: rest => stmtThrows fns s || stmtsThrow fns rest

def clausesThrow (fns : List FnInfo) : List (Option Expr × List Stmt) → Bool
  | [] => false
  | (_, body) :: rest => stmtsThrow fns body || clausesThrow fns rest

end

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

/-- Refuse a call of `fn` that can throw, unless the call is the whole value
of a declaration or a `return` (`top`). The output passes the error of such
a call on with `>>=`, which only a statement can do. `Eval.Stmt.hoisted` has
moved every such call of a function of the file that JS always evaluates into
a declaration of its own, so one that is left stands where JS may not
evaluate it, or calls an imported function, which the hoisting does not
follow yet. -/
def checkThrowingCall (s : Span) (name : String) (fn : FnInfo) (top : Bool) : TM Unit := do
  if fn.throws && !top then
    if fn.file != (← get).file then
      reject s s!"'{name}' is imported and can throw, so a call of it must be the whole value of a const, a let or a return"
    else
      reject s s!"'{name}' can throw, so a call of it may not stand in a branch of ?:, after &&, || or ??, or in an arrow function"
  else pure ()

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

/-- The result of `x`, when `x` gives one that `fits` accepts, or else the
result of `y`, which runs from the state that `x` started from. -/
def firstFitting {A : Type} (x y : TM A) (fits : A → Bool) : TM A := fun s =>
  match x s with
  | .ok a s' => if fits a then .ok a s' else y s
  | .error _ _ => y s

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
  isNumberName name || name == "undefined" || name == "Map" || name == "Set" || name == "Error"

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
  if ctx.typeParams.contains name then
    reject span s!"'{name}' would hide the type parameter {name} in Lean; choose another name"
  checkName span name

def declare (env : Env) (span : Span) (name : String) (binding : Binding) (type : Ty) :
    TM Env := do
  if env.has name then reject span s!"'{name}' shadows a name already in scope"
  -- A local is in its temporal dead zone from the start of its block, so a
  -- use of the name before the declaration throws in JS. The subset reads
  -- such a use as the function or the global, so it refuses the local.
  if env.functions.any (·.name == name) || isGlobalName name then
    reject span s!"'{name}' would hide the function or global {name} in its whole block; choose another name"
  if env.enums.any (·.name == name) then
    reject span s!"'{name}' would hide the enum {name} in its whole block; choose another name"
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

/-- The refusal for a type named with the wrong number of type arguments. -/
def typeArgsMessage (name : String) : Nat → String
  | 0 => s!"'{name}' takes no type arguments"
  | 1 => s!"'{name}' takes 1 type argument"
  | n => s!"'{name}' takes {n} type arguments"

/-- The key type of a map. SameValueZero, which a `Map` compares keys with,
is Lean's equality on bigints, booleans and strings. A `number` key can be
`NaN` or `-0`, which SameValueZero treats apart from `=`, and an object key
compares by identity. -/
def mapKey (s : Span) (k : Ty) (what : String := "a map key") : TM Ty := do
  match k with
  | .bigint | .string | .boolean | .enum _ => return k
  | _ => reject s s!"{what} must be a bigint, a string, a boolean or a literal union of strings"

mutual

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
    if name == "Array" || name == "ReadonlyArray" then return .array (← translateType elem)
    let ctx ← get
    -- `Set<T>` and `ReadonlySet<T>`, unless the program declares a type of
    -- that name.
    if (name == "Set" || name == "ReadonlySet") && (ctx.structs.find? (·.name == name)).isNone &&
        (ctx.aliases.find? (·.name == name)).isNone then
      return .set (← mapKey t.span (← translateType elem) "a set element")
    let args ← translateTypes [elem]
    match ctx.structs.find? (·.name == name), ctx.aliases.find? (·.name == name) with
    | some info, _ =>
      unless info.typeParams.length == 1 do reject t.span (typeArgsMessage name info.typeParams.length)
      return .struct info.ref args
    | none, some info =>
      unless info.typeParams.length == 1 do reject t.span (typeArgsMessage name info.typeParams.length)
      return info.type.subst (info.typeParams.zip args)
    | none, none => unsupportedType t
  | .ref _ name [] =>
    let ctx ← get
    if ctx.typeParams.contains name then return .param name
    match ctx.structs.find? (·.name == name) with
    | some info =>
      unless info.typeParams.isEmpty do reject t.span (typeArgsMessage name info.typeParams.length)
      return .struct info.ref []
    | none =>
      match ctx.enums.find? (·.name == name) with
      | some info => return .enum info.ref
      | none =>
        match ctx.unions.find? (·.name == name) with
        | some info => return .tagged info.ref (info.members.map (·.1))
        | none =>
          match ctx.aliases.find? (·.name == name) with
          | some info =>
            unless info.typeParams.isEmpty do
              reject t.span (typeArgsMessage name info.typeParams.length)
            return info.type
          | none => unsupportedType t
  | .ref s name args =>
    let ctx ← get
    let tys ← translateTypes args
    -- `Map<K, V>` and `ReadonlyMap<K, V>`, unless the program declares a
    -- type of that name.
    if let [k, v] := tys then
      if (name == "Map" || name == "ReadonlyMap") && (ctx.structs.find? (·.name == name)).isNone &&
          (ctx.aliases.find? (·.name == name)).isNone then
        return .map (← mapKey s k) v
    match ctx.structs.find? (·.name == name), ctx.aliases.find? (·.name == name) with
    | some info, _ =>
      unless info.typeParams.length == tys.length do
        reject t.span (typeArgsMessage name info.typeParams.length)
      return .struct info.ref tys
    | none, some info =>
      unless info.typeParams.length == tys.length do
        reject t.span (typeArgsMessage name info.typeParams.length)
      return info.type.subst (info.typeParams.zip tys)
    | none, none => unsupportedType t
  -- A tuple. Lean has no tuple of one element.
  | .tuple s _ elems =>
    if elems.length < 2 then reject s "a tuple needs two elements or more"
    return .tuple (← translateTypes elems)
  | _ => unsupportedType t

def translateTypes : List TypeExpr → TM (List Ty)
  | [] => return []
  | t :: ts => return (← translateType t) :: (← translateTypes ts)

end

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

/-- Every path through `statements` ends in a jump, a statement that
`isJump` accepts. -/
def alwaysEnds (isJump : Stmt → Bool) : List Stmt → Bool
  | [] => false
  | s :: rest => if rest.isEmpty then endsIn isJump s else alwaysEnds isJump rest

/-- `s`, the last statement of a list, ends every path in a jump. -/
def endsIn (isJump : Stmt → Bool) : Stmt → Bool
  | .ifStmt _ _ thenBranch (some elseBranch) =>
    branchEnds isJump thenBranch && branchEnds isJump elseBranch
  | s => isJump s

/-- `alwaysEnds isJump (blockStatements s)`. -/
def branchEnds (isJump : Stmt → Bool) : Stmt → Bool
  | .block _ body => alwaysEnds isJump body
  | .ifStmt _ _ thenBranch (some elseBranch) =>
    branchEnds isJump thenBranch && branchEnds isJump elseBranch
  | s => isJump s

end

/-- Every path through `statements` ends in a `return` or a `throw`, which
both end the function. -/
def alwaysReturns : List Stmt → Bool :=
  alwaysEnds fun s => s matches .returnStmt .. || s matches .throwStmt ..

/-- `s` ends one run of a loop body: a `continue`, a `throw`, or a `break`
or a `return` in a loop that one can end. -/
def isLoopJump (breaks returns : Bool) : Stmt → Bool
  | .continueStmt _ | .throwStmt .. => true
  | .breakStmt _ => breaks
  | .returnStmt .. => returns
  | _ => false

/-- Every path through `statements` ends in a `throw`. -/
def alwaysThrows : List Stmt → Bool :=
  alwaysEnds fun s => s matches .throwStmt ..

mutual

/-- `s` contains a `return`, or a `break` or `continue` that leaves `s`. The
flags say whether a `break` and a `continue` count. Inside a loop that `s`
contains, neither counts, because they leave only that loop. A `throw` is
not a jump here: it ends the function from anywhere, through the `Except`
monad, so a branch or a loop body may hold one. -/
def containsJump (brk cont : Bool) : Stmt → Bool
  | .returnStmt .. => true
  | .breakStmt _ => brk
  | .continueStmt _ => cont
  | .ifStmt _ _ t (some e) => containsJump brk cont t || containsJump brk cont e
  | .ifStmt _ _ t none => containsJump brk cont t
  | .forOfStmt _ _ _ _ body | .forOfPattern _ _ _ _ body | .forStmt _ _ _ _ body | .whileStmt _ _ body =>
    containsJump false false body
  | .block _ body => anyContainsJump brk cont body
  | .switchStmt _ _ clauses => clausesContainJump brk cont clauses
  | _ => false

def anyContainsJump (brk cont : Bool) : List Stmt → Bool
  | [] => false
  | s :: rest => containsJump brk cont s || anyContainsJump brk cont rest

/-- The statements of a clause contain a jump, apart from the `break` they
end in, which leaves only the `switch`. -/
def clauseContainsJump (brk cont : Bool) : List Stmt → Bool
  | [] => false
  | [s] => !s.isBreak && containsJump brk cont s
  | s :: rest => containsJump brk cont s || clauseContainsJump brk cont rest

def clausesContainJump (brk cont : Bool) : List (Option Expr × List Stmt) → Bool
  | [] => false
  | (_, body) :: rest => clauseContainsJump brk cont body || clausesContainJump brk cont rest

end

/-- Why an `if` whose first branch ends in `tail` may not have both an `else`
and statements after it. -/
def Tail.afterEarlyReason : Tail → String
  | .ret => "code after an if whose branches both return or throw is unreachable"
  | _ => "after an if whose first branch ends in continue, break or return, put the code that follows in its else branch"

/-- The tail of the first branch of an `if`, when every path through it,
`thenStatements`, ends the statements that end in `tail`: a `return` or a
`throw` in a function body, a `continue`, `break`, `return` or `throw` in a
loop body, or a `throw` in a branch that ends in its state. A `throw` ends
the function from anywhere, so the branch that throws is translated as the
end of the function; it may hold no other jump, which the function's tail
would also accept. -/
def earlyTail (tail : Tail) (thenStatements : List Stmt) : Option Tail :=
  match tail with
  | .ret => if alwaysReturns thenStatements then some .ret else none
  | .loop names b r | .cont names b r =>
    if alwaysEnds (isLoopJump b r) thenStatements then some (.cont names b r) else none
  | .state _ =>
    if alwaysThrows thenStatements && !anyContainsJump true true thenStatements then some .ret else none

mutual

/-- The names that `e` assigns, increments or pushes to. -/
def exprChanges : Expr → List String
  | .assign _ op target value =>
    let own := match target with
      | .ident _ name => if op.isSimple || op == .coalesce then [name] else []
      | _ => []
    own ++ exprChanges target ++ exprChanges value
  | .prefix _ _ (.ident _ name) | .postfix _ _ (.ident _ name) => [name]
  -- `m.set(k, v)`, `s.add(x)` and `m.delete(k)` change the map or set.
  | .call _ (.member _ (.ident _ name) "set") args | .call _ (.member _ (.ident _ name) "delete") args
  | .call _ (.member _ (.ident _ name) "add") args =>
    name :: exprsChanges args
  | .prefix _ _ e | .postfix _ _ e | .paren _ e | .unary _ _ e | .member _ e _ | .optMember _ e _
  | .asConst _ e | .satisfies _ e _ | .spread _ e =>
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
  | .keyValue _ _ v :: ps | .spread _ v :: ps => exprChanges v ++ propsChanges ps
  | .shorthand .. :: ps => propsChanges ps

end

def optionChanges : Option Expr → List String
  | some e => exprChanges e
  | none => []

mutual

def stmtChanges : Stmt → List String
  | .varDecl _ d => optionChanges d.init
  | .destructure _ _ _ _ init => exprChanges init
  | .exprStmt _ e => exprChanges e
  | .returnStmt _ v => optionChanges v
  | .ifStmt _ test t (some e) => exprChanges test ++ stmtChanges t ++ stmtChanges e
  | .ifStmt _ test t none => exprChanges test ++ stmtChanges t
  | .forOfStmt _ _ _ iterable body | .forOfPattern _ _ _ iterable body =>
    exprChanges iterable ++ stmtChanges body
  | .forStmt _ init test update body =>
    optionChanges (init.bind (·.init)) ++ optionChanges test ++ optionChanges update ++ stmtChanges body
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

/-- `x === undefined` or `x !== undefined`, where `x` is a name in scope with
an optional value, and no local hides `undefined`: `(x, the test is equality,
the type of x when it is defined)`. -/
def undefinedTestOf (env : Env) (e : Expr) : Option (String × Bool × Ty) :=
  if env.has "undefined" then none else
  match e.stripParens with
  | .binary _ op l r =>
    let isEquality? : Option Bool := match op with
      | .strictEq => some true
      | .strictNe => some false
      | _ => none
    match isEquality? with
    | none => none
    | some isEquality =>
      let other? := if r.isUndefinedName then some l else if l.isUndefinedName then some r else none
      match other? with
      | some (.ident _ name) =>
        match env.lookup name with
        | some { type := .optional value, .. } => some (name, isEquality, value)
        | _ => none
      | _ => none
  | _ => none

/-- A test that narrows a name of an `Option` type: `x === null` and the like
on a nullable value, or `x === undefined` and `x !== undefined` on an optional
one. `(x, the test is equality, the type of x when not none, x is optional)`. -/
def noneTestOf (env : Env) (e : Expr) : Option (String × Bool × Ty × Bool) :=
  match nullTestOf env e with
  | some (name, isEquality, value) => some (name, isEquality, value, false)
  | none => (undefinedTestOf env e).map fun (name, isEquality, value) => (name, isEquality, value, true)

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

/-- `clauses` is a `default` clause that checks that the cases before it
cover every member: its first statement is `const x: never = name;`, where
`name` is the local that the `switch` tests. TypeScript accepts it only
where no member is left, so it never runs, and the output leaves it out. -/
def checksNever (name : String) : List (Option Expr × List Stmt) → Bool
  | [(none, body)] =>
    match clauseStatements body with
    | .varDecl _ { kind := .const, type := some (.keyword _ "never"), init := some init, .. } :: _ =>
      match init.stripParens with
      | .ident _ n => n == name
      | _ => false
    | _ => false
  | _ => false

/-- Why a `default` that assigns `name` to `never` is wrong where the
members with the tags `tags` are left. -/
def neverLeftReason (name : String) (tags : List String) : String :=
  s!"'{name}' is not never in this default, because no case takes '{tags.headD ""}'"

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
  | .struct ref [] => do
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
    if (known.find? (·.ref == ref)).any fun i => i.named.isNone && i.members.contains m then
      ⟨.enumCase ref m, false, .enum ref⟩
    else c
  | _, _ => c

/-- How the operands of `a + b`, of the types `s` and `t`, become strings,
when one of them is a string. ToString of a number is not modelled yet. -/
def concatParts? : Ty → Ty → Option (IR.StringPart × IR.StringPart)
  | .string, .string => some (.string, .string)
  | .string, .bigint => some (.string, .bigint)
  | .bigint, .string => some (.bigint, .string)
  | .string, .boolean => some (.string, .boolean)
  | .boolean, .string => some (.boolean, .string)
  | _, _ => none

/-- `a + b` where one operand is a string: ToString converts the other
operand, and the code units join. -/
def concatOperands (s : Span) (a b : Code) : TM Code := do
  let some (left, right) := concatParts? a.type b.type
    | reject s "'+' on a string needs a string, a bigint or a boolean on the other side"
  return ⟨.ext (.stringAppend left right) [a.value, b.value], false, .string⟩

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
    -- Strings compare by their code units, as IsLessThan does.
    if a.type == .string && b.type == .string then
      let le := numberOp == .le
      return if swap then ⟨.ext (.stringOrder le) [b.value, a.value], false, .boolean⟩
        else ⟨.ext (.stringOrder le) [a.value, b.value], false, .boolean⟩
    unless bothBigInt do reject s "ordering needs two bigints, two numbers or two strings"
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
  -- `+` with a string on either side joins strings.
  | .add => if a.type == .string || b.type == .string then concatOperands s a b else arithmetic .add .add
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
  let some (ref, args) := (match t with
      | .nullable (.struct ref args) | .optional (.struct ref args) => some (ref, args)
      | _ => none : Option (DeclRef × List Ty))
    | reject s (if t matches .struct .. then
        "the left side of '?.' is never null or undefined here, so '?.' does nothing; use '.'"
      else "'?.' needs a value of an interface type, or null or undefined")
  let ctx : Ctx ← get
  let field? := (ctx.knownStructs.find? fun (i : StructInfo) => i.ref == ref).bind
    fun info => (info.fieldsAt args).lookup name
  match field? with
  | some (.optional v) => return (true, .optional v)
  | some (.literal _) => reject s "a tag field may be read only in a test of its union, such as x.kind === 'circle'"
  | some v =>
    if v.isNullable then
      reject s "'?.' may not read a nullable field, because the value could be null or undefined"
    return (false, .optional v)
  | none => reject s "only fields of interfaces declared in this file, or exported by the files before it, may be read"

/-- The string enum that `obj` names, as in `T.A`: a name that no local binds.
The interpreter reads a global such as `NaN` before an enum, so an enum may
not have such a name, which `declareTopLevel` refuses too. -/
def enumOf? (env : Env) : Expr → Option EnumValue
  | .ident _ n => if env.has n || isGlobalName n then none else env.enums.find? (·.name == n)
  | _ => none

/-- The function on lists that the method `name` of an array becomes, for the
methods that take a callback. -/
def listMethod? (name : String) : Option IR.ListMethod :=
  if name == "map" then some .map
  else if name == "filter" then some .filter
  else if name == "some" then some .any
  else if name == "every" then some .all
  else if name == "find" then some .find
  else if name == "findIndex" then some .findIndex
  else if name == "findLast" then some .findLast
  else none

/-- The receiver and the method of a call such as `xs.map(…)`, when the
method takes a callback. -/
def arrayMethodOf : Expr → Option (Expr × IR.ListMethod)
  | .member _ recv name => (listMethod? name).map (recv, ·)
  | _ => none

/-- The parameter and the body of the one argument of an array method: an
arrow function with one parameter. -/
def callbackOf : List Expr → Option (Param × Expr)
  | [.arrow _ _ [p] body] => some (p, body)
  | _ => none

/-- The type of the field `key` that a property after a spread sets, where
`seen` are the keys set before it. JS appends a key that the spread did not
copy, and Lean keeps the declared order, so the field may not be optional. A
tag field holds its one string already. -/
def spreadFieldType (structName : String) (fields : List (String × Ty)) (seen : List String) (span : Span)
    (key : String) : TM Ty := do
  let t ← orReject (fields.lookup key) span s!"'{key}' is not a field of {structName}"
  if seen.contains key then reject span s!"'{key}' is set twice"
  if t.isMaybeField then
    reject span s!"'{key}' is optional or a tag; after a spread only a required field may be set"
  return t
/-- The element parameter, the index parameter and the body of the one
argument of `map`, when it is an arrow function with two parameters. -/
def indexedCallbackOf : IR.ListMethod → List Expr → Option (Param × Param × Expr)
  | .map, [.arrow _ _ [p, q] body] => some (p, q, body)
  | _, _ => none

/-- The receiver of a call of `reduce`. -/
def reduceOf : Expr → Option Expr
  | .member _ recv "reduce" => some recv
  | _ => none

/-- The two parameters, the body and the initial value of a call of `reduce`:
an arrow function with two parameters, then a value. -/
def reducerOf : List Expr → Option (Param × Param × Expr × Expr)
  | [.arrow _ _ [a, p] body, init] => some (a, p, body, init)
  | _ => none

/-- `e` is the name `Number`. -/
def _root_.tolean.TypeScript.Syntax.Expr.namesNumber : Expr → Bool
  | .ident _ "Number" => true
  | _ => false

/-- `m.get(k)` and `m.has(k)`, as the method and the operation of the output. -/
def mapMethodOf : Expr → Option (Expr × IR.ExprExt)
  | .member _ recv "get" => some (recv, .mapGet)
  | .member _ recv "has" => some (recv, .mapHas)
  | _ => none

/-- An owned map, which the function may read through `get`, `has` and
`size`: the read does not keep the map, so a later `set` cannot change what
it gives. -/
def ownedMap? (env : Env) : Expr → Option Code
  | .ident _ name =>
    match env.lookup name with
    | some { binding := .map, type, .. } => some ⟨.var name, false, type⟩
    | _ => none
  | _ => none

/-- How a local that `kind` declares with the value `init` may be used.
`const m = new Map()` is an owned map, which the function may change with
`set` and `delete`, and `const s = new Set()` an owned set. A map in a `let`
is a value: the `let` could later name another map, which the function does
not own. -/
def varBinding (kind : VarKind) (init : Expr) : Binding :=
  match kind, init with
  | .const, .new _ "Map" _ _ | .const, .new _ "Set" _ _ => .map
  | .const, _ => .const
  | .«let», _ => .«let»

/-- The type of `new Map<K, V>()`: the type arguments, or the map type that
the context expects. -/
def newMapType (s : Span) (typeArgs : List TypeExpr) (expected : Option Ty) : TM Ty := do
  match typeArgs, expected with
  | [k, v], _ => return .map (← mapKey s (← translateType k)) (← translateType v)
  | [], some (.map k v) => return .map k v
  | _, _ => reject s "new Map needs the types of its keys and values, such as new Map<string, bigint>()"

/-- The map type of `new Map<K, V>(items)` that the type arguments or the
context give, if they give one. -/
def declaredMapType (s : Span) (typeArgs : List TypeExpr) (expected : Option Ty) : TM (Option Ty) := do
  match typeArgs, expected with
  | [k, v], _ => return some (.map (← mapKey s (← translateType k)) (← translateType v))
  | [], some (.map k v) => return some (.map k v)
  | [], _ => return none
  | _, _ => reject s "Map takes two type arguments"

/-- The set type of `new Set<T>(items)` that the type argument or the context
give, if they give one. -/
def declaredSetType (s : Span) (typeArgs : List TypeExpr) (expected : Option Ty) : TM (Option Ty) := do
  match typeArgs, expected with
  | [t], _ => return some (.set (← mapKey s (← translateType t) "a set element"))
  | [], some (.set t) => return some (.set t)
  | [], _ => return none
  | _, _ => reject s "Set takes one type argument"

/-- What the argument of `new Map` is translated for: an array of entries. -/
def Ty.entriesOf : Ty → Ty
  | .map k v => .array (.tuple [k, v])
  | t => t

/-- What the argument of `new Set` is translated for: an array of elements. -/
def Ty.elemsOf : Ty → Ty
  | .set t => .array t
  | t => t

/-- The type of `new Map(items)`, where `items` visits values of type `elem`. -/
def mapOfEntriesType (s : Span) (declared : Option Ty) (elem : Ty) : TM Ty := do
  match declared, elem with
  | some (.map k v), _ =>
    unless elem == .tuple [k, v] do reject s "the entries do not have the key and value types of the map"
    return .map k v
  | none, .tuple [k, v] => return .map (← mapKey s k) v
  | _, _ => reject s "new Map takes an array of [key, value] entries, or a map"

/-- The type of `new Set(items)`, where `items` visits values of type `elem`. -/
def setOfElemsType (s : Span) (declared : Option Ty) (elem : Ty) : TM Ty := do
  match declared with
  | some (.set t) =>
    unless elem == t do reject s "the elements do not have the element type of the set"
    return .set t
  | _ => return .set (← mapKey s elem "a set element")

/-- The type of `new Set<T>()`: the type argument, or the set type that the
context expects. -/
def newSetType (s : Span) (typeArgs : List TypeExpr) (expected : Option Ty) : TM Ty := do
  match typeArgs, expected with
  | [t], _ => return .set (← mapKey s (← translateType t) "a set element")
  | [], some (.set t) => return .set t
  | _, _ => reject s "new Set needs the type of its elements, such as new Set<string>()"

/-- What `for (const x of items)` visits, with its type: the elements of an
array or a set, or the entries of a map, which a loop sees as tuples
`[key, value]`. -/
def loopOver (items : Code) : Option (Ty × IR.Expr) :=
  match items.type with
  | .array t => some (t, items.code)
  | .set t => some (t, .ext .setElems [items.value])
  | .map k v => some (.tuple [k, v], .ext .mapEntries [items.value])
  | _ => none

/-- What a loop over `iterable`, which `items` translates, visits, when the
loop body is `body`. -/
def loopItems (iterable : Expr) (body : Stmt) (items : Code) : TM (Ty × IR.Expr) := do
  if Stmt.mutatesIterable iterable body then
    reject iterable.span "a loop may not change the map or set that it runs over"
  orReject (loopOver items) iterable.span "a loop must run over an array, a set or a map"

/-- A piece of an array literal: an element, or the list of values that a
spread `...e` gives, with their type. -/
inductive ElemPart where
  | one (c : Code)
  | many (elem : Ty) (items : IR.Expr)

/-- The piece as a `Code`, for `elementType`, which reads only its type. -/
def ElemPart.asCode : ElemPart → Code
  | .one c => c
  | .many t items => ⟨items, false, t⟩

/-- An element of an array literal, where `expected` is the type of the array
when the context gives one, and `tr` translates an expression. A spread
`...e` iterates `e` (ECMA-262 §13.2.4.1), so it gives the values that a loop
over `e` visits: the elements of an array or a set, or the entries of a map. -/
def translateElem (tr : Option Ty → Expr → TM Code) (expected : Option Ty) (e : Expr) :
    TM ElemPart :=
  match e.spreadArg? with
  | some (sp, x) => do
    let items ← tr expected x
    let (t, li) ← orReject (loopOver items) sp "a spread '...' in an array needs an array, a set or a map"
    pure (.many t li)
  | none => do
    let elem := match expected with
      | some (.array t) => some t
      | _ => none
    pure (.one (← tr elem e))

/-- The lists that the output joins with `++`: each spread's list, and one
literal for each run of elements between them. -/
def partLists (t : IR.Ty) : List ElemPart → List IR.Expr
  | [] => []
  | .many _ items :: ps => items :: partLists t ps
  | .one c :: ps =>
    match partLists t ps with
    | .list xs _ :: rest => .list (c.value :: xs) t :: rest
    | rest => .list [c.value] t :: rest

/-- Each piece has the array's element type `elem`. An element may have a
type that fits `elem`, which Lean converts it to in the literal, but Lean does
not convert the elements of a list, so a spread must have `elem` itself. -/
def checkParts (elem : Ty) : List (ElemPart × Expr) → TM Unit
  | [] => pure ()
  | (.one c, e) :: ps => do
    unless c.type.assignableTo elem do reject e.span "the element does not have the array's element type"
    checkParts elem ps
  | (.many t _, e) :: ps => do
    unless t == elem do reject e.span "the spread's elements do not have the array's element type"
    checkParts elem ps

/-- An array literal with a spread, such as `[...xs, x]`: `xs ++ [x]`. The
element type comes from the context, or else from the elements and the
spreads. -/
def translateSpreadArray (tr : Option Ty → Expr → TM Code) (expected : Option Ty) (s : Span)
    (elems : List Expr) : TM Code := do
  let parts ← elems.mapM (translateElem tr expected)
  let expectedElem := match expected with
    | some (.array t) => some t
    | _ => none
  let elem ← elementType s expectedElem (parts.map ElemPart.asCode)
  checkParts elem (parts.zip elems)
  return ⟨.ext .append (partLists elem.lean parts), false, .array elem⟩

/-- The receiver of `size`, `get` or `has`: an owned map as its local, as
`ownedMap?` reads it, and any other expression as `tr` translates it. -/
def translateRecv (tr : Expr → TM Code) (env : Env) (e : Expr) : TM Code :=
  match ownedMap? env e with
  | some c => pure c
  | none => tr e

/-- `new Map()` or `new Set()`, a map or a set without entries, or
`new Map(items)` or `new Set(items)`, which sets each `[key, value]` or adds
each value that `items` visits. `tr` translates an expression where a type is
expected. The type comes from the type arguments, or from the context, as in
`const m: Map<K, V> = new Map()`, or else from `items`. -/
def translateNew (tr : Option Ty → Expr → TM Code) (env : Env) (expected : Option Ty) (s : Span)
    (callee : String) (typeArgs : List TypeExpr) (args : List Expr) : TM Code := do
  let isMap := callee == "Map"
  unless isMap || callee == "Set" do reject s "only new Map() and new Set() are supported"
  if env.has callee then reject s s!"a local named {callee} hides the global {callee}"
  match args with
  | [] =>
    let type ← if isMap then newMapType s typeArgs expected else newSetType s typeArgs expected
    return ⟨.ascribe (.ext (if isMap then .mapEmpty else .setEmpty) []) type.lean, false, type⟩
  | [arg] =>
    let declared ← if isMap then declaredMapType s typeArgs expected else declaredSetType s typeArgs expected
    let items ← translateRecv (tr (declared.map fun t => if isMap then t.entriesOf else t.elemsOf)) env arg
    let (elem, li) ← orReject (loopOver items) arg.span
      (if isMap then "new Map takes an array of [key, value] entries, or a map"
       else "new Set takes an array or a set")
    let type ← if isMap then mapOfEntriesType arg.span declared elem else setOfElemsType arg.span declared elem
    return ⟨.ascribe (.ext (if isMap then .mapOfList else .setOfList) [li]) type.lean, false, type⟩
  | _ => reject s s!"new {callee} takes at most one argument"

/-- The element type of an array. -/
def Ty.element? : Ty → Option Ty
  | .array t => some t
  | _ => none

/-- `xs[k]` with a number literal `k`, on the array `xs` of elements of type
`elem`. A number literal is the integer it names, whatever the model of
numbers. -/
def indexLiteral (s : Span) (text : String) (xs : Code) (elem : Ty) : TM Code := do
  let k ← orReject (safeIntegerValue? text) s "a number literal must be a safe integer"
  unless 0 ≤ k do reject s "an index must not be negative"
  -- `xs[k]?` needs its type written out: Lean picks the element type from
  -- the context first, which can be wrong, as in `let v := xs[1]?`.
  return ⟨.ascribe (.ext (.indexLit k.toNat) [xs.value]) (Ty.optional elem).lean, false, .optional elem⟩

/-- `xs[i]` with the code `i` of a number. -/
def indexNumber (s : Span) (xs i : Code) (elem : Ty) : TM Code := do
  unless i.type == .number do reject s "the index of an array must be a number"
  return ⟨.ext .indexNumber [xs.value, i.value], false, .optional elem⟩

/-- The receiver and the method of a call such as `xs.includes(v)`, for a
method that takes no callback. `Number.isNaN(x)` and the like are calls of the
global `Number`, not of an array. -/
def arrayCallOf : Expr → Option (Expr × String)
  | .member _ recv name => if recv.namesNumber then none else some (recv, name)
  | _ => none

/-- The start and the end of `slice`, from the integers of its arguments: a
missing start is `0`, and a missing end is none, the length. -/
def sliceBounds : List Int → Option (Int × Option Int)
  | [] => some (0, none)
  | [k] => some (k, none)
  | [k, e] => some (k, some e)
  | _ => none

/-- `e` is an arrow function. -/
def _root_.tolean.TypeScript.Syntax.Expr.isArrow : Expr → Bool
  | .arrow .. => true
  | _ => false

/-- The method of a string that `name` names, among those the subset has. -/
def stringMethod? (name : String) : Option IR.StringMethod :=
  if name == "startsWith" then some .startsWith
  else if name == "endsWith" then some .endsWith
  else if name == "includes" then some .includes
  else if name == "indexOf" then some .indexOf
  else if name == "trim" then some .trim
  else if name == "trimStart" then some .trimStart
  else if name == "trimEnd" then some .trimEnd
  else if name == "split" then some .split
  else none

/-- The types of the arguments that a method of a string takes here. JS converts
another argument with ToString, which the subset has only on strings, and a
position argument is not supported. -/
def StringMethod.params : IR.StringMethod → List Ty
  | .startsWith | .endsWith | .includes | .indexOf | .split => [.string]
  | .trim | .trimStart | .trimEnd => []

/-- The type of the value of a method of a string. -/
def StringMethod.result : IR.StringMethod → Ty
  | .startsWith | .endsWith | .includes => .boolean
  | .indexOf => .number
  | .trim | .trimStart | .trimEnd => .string
  | .split => .array .string

/-- The edition from which a method of a string means what the model says,
when that is later than ES2015. -/
def StringMethod.feature : IR.StringMethod → Option Feature
  | .trim => some .trimWhiteSpace
  | .trimStart | .trimEnd => some .trimStartEnd
  | _ => none

/-- Refuse the code when the target does not have `f`. -/
def requireFeature? (s : Span) : Option Feature → TM Unit
  | some f => requireFeature s f
  | none => pure ()

/-- The code for `str.method(args)`, a method of a string, where `str` is the
code of the receiver and `args` are the codes of the arguments. -/
def stringCall (s : Span) (method : String) (str : Code) (args : List Code) : TM Code :=
  if str.type == .string then
    match stringMethod? method with
    | some m =>
      if args.length == (StringMethod.params m).length then
        if args.map (·.type) == StringMethod.params m then do
          requireFeature? s (StringMethod.feature m)
          return ⟨.ext (.stringMethod m) (str.value :: args.map (·.value)), false, StringMethod.result m⟩
        else reject s s!"the argument of '{method}' must be a string"
      else reject s (if (StringMethod.params m).isEmpty then s!"'{method}' takes no arguments"
        else if m == .split then s!"'{method}' takes one string here; a limit is not supported"
        else s!"'{method}' takes one string here; a position argument is not supported")
    | none => reject s s!"the string method '{method}' is not supported here"
  else reject s s!"only a string has the method '{method}' here"

/-- The type that the context gives the arguments of the array method
`method` on elements of type `elem`: for `includes`, the element type, so that
a string can be a constructor of a literal union. -/
def arrayArgExpected (method : String) (elem : Ty) : Option Ty :=
  if method == "includes" then some elem else none

/-- The operation that `xs.includes(x)` becomes on elements of type `elem`.
SameValueZero is `=` on integers, booleans, strings and the constructors of a
literal union. On numbers it is `JSNumber.eq`, except that `NaN` is the same
as `NaN`. On objects it compares identities, which the output cannot. -/
def includesOp? (elem : Ty) : Option IR.ExprExt :=
  if elem == .number then some .includesNumber
  else if elem.isEqPrimitive then some .includes
  else none

/-- The code for `xs.method(args)`, a method of an array that takes no
callback, where the elements of `xs` have the type `elem` and `args` are the
codes of the arguments. -/
def arrayCall (s : Span) (method : String) (elem : Ty) (xs : Code) (args : List Code) : TM Code := do
  if method == "includes" then
    let [x] := args
      | reject s "'includes' takes one argument here; the index to start at is not supported"
    unless x.type == elem do reject s "the argument of 'includes' must have the element type of the array"
    requireFeature s .arrayIncludes
    let op ← orReject (includesOp? elem) s
      "'includes' needs an array of numbers, bigints, booleans, strings or a literal union"
    -- `x ∈ xs` is a `Prop`.
    return ⟨.ext op [xs.value, x.value], op == .includes, .boolean⟩
  reject s s!"the array method '{method}' is not supported here"

/-- A callback's parameter may have a type written out: the element type. -/
def checkParamType (p : Param) (elem : Ty) : TM Unit := do
  if let some t := p.type then
    unless (← translateType t) == elem do
      reject p.span "the parameter must have the element type of the array"

/-- The first parameter of the callback of `reduce`, if it has a type, has the
type of the initial value. -/
def checkAccType (a : Param) (accType : Ty) : TM Unit := do
  if let some t := a.type then
    unless (← translateType t) == accType do
      reject a.span "the first parameter of 'reduce' must have the type of the initial value"

/-- The index parameter of a callback of `map`, if it has a type, has the type
`number`. -/
def checkIndexType (q : Param) : TM Unit := do
  if let some t := q.type then
    unless (← translateType t) == .number do reject q.span "the index of an array is a number"

/-- The type that the body of a callback is translated for: for `map`, the
element type of the array that the context expects, which an object literal
needs. -/
def callbackExpected : IR.ListMethod → Option Ty → Option Ty
  | .map, some (.array t) => some t
  | _, _ => none

/-- The type of `xs.method(cb)`, where the elements of `xs` have the type
`elem` and the body of `cb` has the type `body`. -/
def callbackResult (s bodySpan : Span) (method : IR.ListMethod) (elem body : Ty) : TM Ty := do
  if method == .map then
    if body == .null || body matches .optional _ || body matches .literal _ then
      reject bodySpan "the callback of 'map' must give a value of a type that an array can hold"
    return .array body
  unless body == .boolean do reject bodySpan "the callback must give a boolean"
  match method with
  | .filter => return .array elem
  | .find | .findLast =>
    if method == .findLast then requireFeature s .arrayFindLast
    -- The output has one `none` for `undefined` and `null`.
    if elem.isNullable || elem matches .optional _ then
      reject s "'find' on an array of nullable values could give null or undefined"
    return .optional elem
  | .findIndex => return .number
  | _ => return .boolean

/-- The type of `x.f1.f2…` after `?.`, where `x` has the interface `ref`:
whether the last field is optional, and the type of the chain. Each field
before the last must be a required field of an interface type, because
`.` on `null` or `undefined` throws. -/
def optPathRest (s : Span) (ref : DeclRef) (args : List Ty) : List String → TM (Bool × Ty)
  | [] => reject s "a chain after '?.' must read a property"
  | [f] => optFieldType s (.nullable (.struct ref args)) f
  | f :: rest => do
    let ctx : Ctx ← get
    let field? := (ctx.knownStructs.find? fun (i : StructInfo) => i.ref == ref).bind
      fun info => (info.fieldsAt args).lookup f
    match field? with
    | some (.struct ref' args') => optPathRest s ref' args' rest
    | some (.optional _) | some (.nullable _) =>
      reject s s!"'{f}' may be null or undefined, so the property after it needs '?.' too"
    | some _ => reject s s!"a property after '{f}' needs a value of an interface type"
    | none => reject s "only fields of interfaces declared in this file, or exported by the files before it, may be read"

/-- The type of `x?.f1.f2…` on a value of type `t`: whether the last field is
optional, and the type of the chain, which is `undefined` when `x` is
`null` or `undefined`. -/
def optPathType (s : Span) (t : Ty) : List String → TM (Bool × Ty)
  | [] => reject s "a chain after '?.' must read a property"
  | [f] => optFieldType s t f
  | f :: rest => do
    let (bind, ft) ← optFieldType s t f
    if bind then reject s s!"'{f}' may be undefined, so the property after it needs '?.' too"
    let .optional (.struct ref args) := ft
      | reject s s!"a property after '{f}' needs a value of an interface type"
    optPathRest s ref args rest

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
  -- Parentheses and `as const` pass the operand on before it becomes a member
  -- of a union, so that `(s) satisfies U` keeps the type of `s`, as
  -- `s satisfies U` does. `translateExpr` makes the whole expression a member
  -- once, where the context expects the union.
  | .paren _ inner => translateExprCore fuel env expected inner
  -- Type stripping removes `as const`, which only keeps the literal types of
  -- the value. The output types a literal by its context, as without it.
  | .asConst _ inner => translateExprCore fuel env expected inner
  -- `satisfies T` checks the value against `T`, and the value keeps its own
  -- type. A member of a union of primitive types is checked as the union's
  -- constructor would be, but it does not become one, so `s satisfies U` and
  -- `(b ? s : t) satisfies U` are still a `string`. The value is typed in the
  -- context of `T` only when it needs a context to be typed at all, as an
  -- object literal does, or when its own type does not fit `T`, as a string
  -- literal of a literal union does not.
  | .satisfies s inner type =>
    let t ← translateType type
    let fits (c : Code) : Bool := c.type.fits env.unions t
    let code ← firstFitting (translateExprCore fuel env none inner)
      (translateExprCore fuel env (some t) inner) fits
    unless fits code do
      reject s "the value does not have the type that 'satisfies' names"
    return code
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
      if info.named.isSome then
        reject s s!"a value of the enum {info.name} is one of its members, such as {info.name}.A, not a string"
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
      -- `undefined` where an optional value is expected, such as the
      -- argument of an optional parameter. A field of an object literal
      -- expects the type of the value that it holds, so it refuses
      -- `undefined`: JS tells a key that holds it from a missing key.
      if name == "undefined" then
        let some (.optional t) := expected
          | reject s "undefined may stand only where an optional value is expected, such as the argument of an optional parameter"
        return ⟨.undefined, false, .optional t⟩
      let some constant := numberConstant? name
        | reject s "only parameters and locals may be referenced"
      return ⟨.numberConstant constant, false, .number⟩
    | some l =>
      if l.binding == .array && !(← get).returning then
        reject s "an owned array may be read only in the return value"
      if l.binding == .map && !(← get).returning then
        reject s "an owned map or set may be read only through get, has and size, or in the return value"
      return ⟨.var name, false, l.type⟩
  | .member s obj name =>
    match enumOf? env obj with
    -- `T.A`, a member of a string enum: its string, which the output writes
    -- as the constructor that the string names.
    | some e =>
      let value ← orReject (e.members.lookup name) s s!"'{name}' is not a member of the enum {e.name}"
      return ⟨.enumCase e.ref value, false, .enum e.ref⟩
    | none =>
    -- A read after `?.` is a part of the optional chain, so `a?.b.c` is one
    -- `map` over `a`, not `(a?.b).c`.
    if obj.optSpine then
      let some (base, path) := (Expr.member s obj name).optChain?
        | reject s "a chain after '?.' must read a property"
      let o ← translateExpr fuel env none base
      let (bind, type) ← optPathType s o.type path
      return ⟨.ext (.optField path bind) [o.code], false, type⟩
    let o ← translateRecv (translateExpr fuel env none) env obj
    -- `xs.length`, the number of elements of an array.
    if o.type.element?.isSome && name == "length" then
      return ⟨.ext .length [o.value], false, .number⟩
    -- `m.size`, the number of entries of a map.
    if let .map _ _ := o.type then
      unless name == "size" do reject s "a map has no fields here; use get, has and size"
      return ⟨.ext .mapSize [o.value], false, .number⟩
    -- `s.length`: the number of code units of a string (ECMA-262 §22.1.4.1).
    if let .string := o.type then
      unless name == "length" do reject s s!"a string has no property '{name}' here, only 'length'"
      return ⟨.ext .stringLength [o.value], false, .number⟩
    -- `s.size`, the number of elements of a set.
    if let .set _ := o.type then
      unless name == "size" do reject s "a set has no fields here; use has and size"
      return ⟨.ext .setSize [o.value], false, .number⟩
    let ctx : Ctx ← get
    let field? := match o.type with
      | .struct ref args =>
        (ctx.knownStructs.find? fun (i : StructInfo) => i.ref == ref).bind
          fun info => (info.fieldsAt args).lookup name
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
    return ⟨.ext (.optField [name] bind) [o.code], false, type⟩
  | .index s obj key =>
    let o ← translateExpr fuel env none obj
    match o.type.tupleElems? with
    -- `t[0]`: an element of a tuple, at an index that is a number literal.
    | some tys =>
      let .number _ text := key | reject key.span "the index of a tuple must be a number literal, such as t[0]"
      let i ← orReject (safeIntegerValue? text) key.span "the index of a tuple must be an integer"
      match tys[i.toNat]? with
      | some t =>
        unless 0 ≤ i do reject key.span s!"the tuple has no element {i}"
        return ⟨.proj o.code i.toNat tys.length, false, t⟩
      | none => reject key.span s!"the tuple has no element {i}"
    | none =>
    match o.type.element? with
    -- `xs[i]` on an array: the element, or `undefined` when `i` is not an
    -- index of the array. So its type is that of an optional field, which
    -- `??`, `?.` and `=== undefined` read.
    | some elem => translateArrayIndex fuel env s o elem key
    -- `r[k]` on a `Record<K, V>`.
    | none =>
      let (keyRef, keys, type) ← orReject (recordIndex (← get) o.type) s
        ("only an array, a tuple, or a value of a Record type, such as type T = Record<K, V>, whose key type K " ++
          "this file declares or imports, may be indexed")
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
  | .call s callee args =>
    match reduceOf callee with
    | some recv => translateReduce fuel env expected s recv args
    | none =>
    match arrayMethodOf callee with
    | some (recv, method) => translateArrayMethod fuel env expected s recv method args
    | none =>
      match mapMethodOf callee with
      | some (recv, op) => translateMapMethod fuel env s recv op args
      | none =>
        match arrayCallOf callee with
        | some (recv, method) => translateArrayCall fuel env s recv method args
        | none => translateCall fuel env s callee args false
  -- `new Map()` and `new Set()`, with or without the values to start with.
  | .new s callee typeArgs args =>
    translateNew (fun exp e => translateExpr fuel env exp e) env expected s callee typeArgs args
  | .object s props =>
    match spreadOf props with
    | some (base, rest) => translateSpread fuel env s base rest
    | none => translateObject fuel env expected s props
  | .array s elems =>
    match expected with
    | some (.tuple tys) =>
      -- A tuple: each element where its own type is expected. In JS the
      -- tuple is an array.
      unless elems.length == tys.length do reject s s!"the tuple needs {tys.length} elements"
      -- An element where the type names a type parameter has its own type,
      -- which the context checks: a call, after it fixes the parameter, or a
      -- return or a declaration in a generic function. A `null` keeps its
      -- own type, so that in a `T | null` it leaves `T` to the other
      -- arguments of a call. Another element that fits takes the type of its
      -- place, which Lean converts it to in the literal.
      let codes ← (elems.zip tys).mapM fun (elem, t) => do
        let a ← translateExpr fuel env (if t.isGeneric then t.callExpected else some t) elem
        unless t.isGeneric || a.type.assignableTo t do
          reject elem.span "the element does not have the tuple's element type"
        pure a
      let types := (codes.zip tys).map fun (a, t) =>
        if !t.isGeneric then t
        else if a.type == .null || !a.type.assignableTo t then a.type
        else t
      return ⟨.tuple (codes.map (·.value)), false, .tuple types⟩
    | _ => translateArray fuel env expected s elems
  -- An array literal translates its own spreads; a tuple literal and the
  -- arguments of a call do not take one yet.
  | .spread sp _ => reject sp "a spread '...' may only be an element of an array literal"
  | _ => reject e.span "unsupported expression"

/-- An array literal, as a list. In JS a literal makes a new array, and only
an owned array may be pushed to, so nothing changes the array after it is
made, and a Lean list has its meaning. The element type comes from the
context, or else from the elements. A literal with a spread, such as
`[...xs, x]`, joins lists with `++` (`translateSpreadArray`). -/
def translateArray (fuel : Nat) (env : Env) (expected : Option Ty) (s : Span) (elems : List Expr) :
    TM Code := do
  let fuel + 1 := fuel | tooDeep
  if elems.any (·.spreadArg?.isSome) then
    translateSpreadArray (translateExpr fuel env) expected s elems
  else
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

def translateCall (fuel : Nat) (env : Env) (s : Span) (callee : Expr) (args : List Expr) (top : Bool) :
    TM Code := do
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
    "calls may name only the function itself, functions declared earlier in this file, or imported ones"
  let noCall {A : Type} : TM A := reject s noCallMessage
  let .ident _ name := callee | noCall
  if (name == "isNaN" || name == "isFinite") && !env.functions.any (·.name == name) then
    reject s s!"the global {name} converts its argument to a number; use Number.{name}"
  let fn ← orReject (env.functions.find? (·.name == name)) s noCallMessage
  if env.has name then noCall
  checkThrowingCall s name fn top
  -- A call may leave out optional parameters, which come last. Each is
  -- `undefined` then, and the output passes `none` for it.
  let required := (fn.params.filter fun t => !(t matches .optional _)).length
  unless args.length ≤ fn.params.length && (fn.params.drop args.length).all (· matches .optional _) do
    reject s (if required == fn.params.length then s!"'{name}' takes {fn.params.length} arguments"
      else s!"'{name}' takes {required} to {fn.params.length} arguments")
  -- An argument is translated where its parameter's type is expected. When
  -- that type names a type parameter, the arguments' types fix it, and only
  -- the shape of a tuple is expected. `undefined`, with or without
  -- parentheses, is read where the optional parameter's type is expected, as
  -- for a call that leaves the argument out. Its type then names the type
  -- parameters, which the other arguments fix. Each argument is translated
  -- once, because a second translation would double the work of each nested
  -- call.
  let undefinedArg (arg : Expr) (paramType : Ty) : Bool :=
    arg.stripParens.isUndefinedName && !env.has "undefined" && paramType matches .optional _
  let first ← (args.zip fn.params).mapM fun (arg, paramType) =>
    translateExpr fuel env (if undefinedArg arg paramType then some paramType else paramType.callExpected) arg
  let known := fixedParams fn.params first
  (args.zip first).forM fun (arg, c) => do
    if c.unfixedBy known then
      reject arg.span "undefined may stand only where an optional value is expected, such as the argument of an optional parameter, and the other arguments must fix its type"
  let codes := fixArgs fn.params first
  let sol := Ty.unifyList [] fn.params (codes.map (·.type))
  fn.typeParams.forM fun v => do
    unless (sol.lookup v).isSome do
      reject s s!"the arguments do not fix the type parameter {v} of '{name}'"
  (args.zip (codes.zip fn.params)).forM fun (arg, c, paramType) => do
    unless c.type.passableTo (paramType.subst sol) do
      reject arg.span "the argument does not have the parameter's type"
  let missing := (fn.params.drop args.length).map fun _ => IR.Expr.undefined
  return ⟨.call fn.ref (optArgs sol codes fn.params ++ missing), false, fn.ret.subst sol⟩

/-- The arguments of a call, with the type of each argument of an optional
parameter that names a type parameter written out: `(v : Option T)` with the
types that the call fixes. Lean then makes a plain `v` the `some` of it, and
knows the type of a `none`, where it could not infer `T` from the rest of
the call. -/
def optArgs (sol : List (String × Ty)) : List Code → List Ty → List IR.Expr
  | c :: cs, p :: ps =>
    (if p matches .optional _ && p.isGeneric then .ascribe c.value (p.subst sol).lean else c.value) ::
      optArgs sol cs ps
  | cs, [] => cs.map (·.value)
  | [], _ :: _ => []

/-- `xs.map(x => e)`, and `filter`, `some`, `every` and `find`: the `List`
function with `fun (x : T) => e`. The callback is an arrow function written at
the call, so it sees the locals of the call, and its body is an expression,
which changes no local. JS also passes the index and the array, which a
callback with one parameter ignores. -/
def translateArrayMethod (fuel : Nat) (env : Env) (expected : Option Ty) (s : Span) (recv : Expr)
    (method : IR.ListMethod) (args : List Expr) : TM Code := do
  let fuel + 1 := fuel | tooDeep
  -- `xs.map((x, i) => e)` becomes `List.mapIdx`, whose function binds the
  -- index as a number.
  if let some (p, q, body) := indexedCallbackOf method args then
    if recv.namesNumber then reject recv.span "only an array has this method"
    let xs ← translateExpr fuel env none recv
    let elem ← orReject xs.type.element? recv.span "only an array has this method"
    checkParamType p elem
    checkIndexType q
    let withIndex ← declare env q.span q.name .param .number
    let inner ← declare withIndex p.span p.name .param elem
    let b ← translateExpr fuel inner (callbackExpected .map expected) body
    let type ← callbackResult s body.span .map elem b.type
    let info : IR.CallbackInfo IR.TyExt :=
      { span := s, result := b.type.lean, scope := env.locals.map fun l => (l.name, l.type.lean) }
    return ⟨.listMethod (.mapIdx q.name) xs.value p.name elem.lean b.value info, false, type⟩
  let (p, body) ← orReject (callbackOf args) s
    ("an array method here takes one arrow function with one parameter, such as " ++
      "xs.map(x => x + 1n). Only the callback of map may also take the index, " ++
      "and no callback may take the array yet")
  -- `Number.map` is a property of the global `Number`, not of an array.
  if recv.namesNumber then reject recv.span "only an array has this method"
  let xs ← translateExpr fuel env none recv
  let elem ← orReject xs.type.element? recv.span "only an array has this method"
  checkParamType p elem
  let inner ← declare env p.span p.name .param elem
  let b ← translateExpr fuel inner (callbackExpected method expected) body
  let type ← callbackResult s body.span method elem b.type
  let info : IR.CallbackInfo IR.TyExt :=
    { span := s, result := b.type.lean, scope := env.locals.map fun l => (l.name, l.type.lean) }
  return ⟨.listMethod method xs.value p.name elem.lean b.value info, false, type⟩

/-- `xs[i]` on an array whose code is `o` and whose elements have the type
`elem`: the element, or `undefined` when `i` is not an index of the array. -/
def translateArrayIndex (fuel : Nat) (env : Env) (s : Span) (o : Code) (elem : Ty) (key : Expr) :
    TM Code := do
  let fuel + 1 := fuel | tooDeep
  -- The output has one `none` for `undefined` and `null`.
  if elem.isMaybe then reject s "an index of an array of nullable values could give null or undefined"
  match key with
  | .number _ text => indexLiteral key.span text o elem
  | _ => indexNumber key.span o (← translateExpr fuel env none key) elem

/-- `xs.includes(v)` or `s.startsWith(p)`, a method of an array or a string that
takes no callback: the receiver, then each argument, then `arrayCall` or
`stringCall` on their codes. An arrow function is a callback, which no such
method takes. -/
def translateArrayCall (fuel : Nat) (env : Env) (s : Span) (recv : Expr) (method : String)
    (args : List Expr) : TM Code := do
  let fuel + 1 := fuel | tooDeep
  if args.any (·.isArrow) then reject s s!"'{method}' does not take a callback here"
  let xs ← translateExpr fuel env none recv
  if xs.type == .string then
    let codes ← args.mapM (translateExpr fuel env none)
    stringCall s method xs codes
  else
  let elem ← orReject xs.type.element? recv.span "only an array or a string has this method"
  -- `xs.at(k)`: the element at `k`, counted from the end when `k` is
  -- negative, or `undefined`. The model of numbers cannot truncate yet, so
  -- the argument must be an integer literal, which is the integer it names.
  if method == "at" then
    let [arg] := args | reject s "'at' takes one argument"
    let k ← orReject (Eval.intLiteral? arg) arg.span
      "the argument of 'at' must be an integer literal, such as xs.at(-1)"
    requireFeature s .arrayAt
    if elem.isMaybe then reject s "'at' on an array of nullable values could give null or undefined"
    return ⟨.ascribe (.ext (.at k) [xs.value]) (Ty.optional elem).lean, false, .optional elem⟩
  -- `xs.slice(start, end)`: a new array of the elements from `start` up to
  -- `end`, where a negative bound counts from the end. The bounds must be
  -- integer literals, as the argument of `at` must.
  if method == "slice" then
    let bounds ← orReject (args.mapM Eval.intLiteral?) s
      "the arguments of 'slice' must be integer literals, such as xs.slice(1) or xs.slice(-2)"
    let (start, stop) ← orReject (sliceBounds bounds) s "'slice' takes at most two arguments"
    if start < 0 && stop.any (0 ≤ ·) then
      reject s ("'slice' with a negative start and an end that is not negative is not supported; " ++
        "write both bounds from the start or both from the end")
    return ⟨.ext (.slice start stop) [xs.value], false, xs.type⟩
  let codes ← args.mapM (translateExpr fuel env (arrayArgExpected method elem))
  arrayCall s method elem xs codes

/-- `xs.reduce((acc, x) => e, init)`: `List.foldl (fun acc x => e) init xs`.
The value so far has the type of `init`, and the body must give that type.
JS also passes the index and the array, which a callback with two parameters
ignores. -/
def translateReduce (fuel : Nat) (env : Env) (expected : Option Ty) (s : Span) (recv : Expr)
    (args : List Expr) : TM Code := do
  let fuel + 1 := fuel | tooDeep
  let (a, p, body, init) ← orReject (reducerOf args) s
    ("'reduce' takes an arrow function with two parameters and an initial value, " ++
      "such as xs.reduce((sum, x) => sum + x, 0n)")
  if recv.namesNumber then reject recv.span "only an array has this method"
  let xs ← translateExpr fuel env none recv
  let elem ← orReject xs.type.element? recv.span "only an array has this method"
  let i ← translateExpr fuel env expected init
  let accType := i.type
  if accType == .null || accType.isLiteral then
    reject init.span "the initial value of 'reduce' needs a type that a local can have"
  checkAccType a accType
  checkParamType p elem
  let withAcc ← declare env a.span a.name .param accType
  let inner ← declare withAcc p.span p.name .param elem
  let b ← translateExpr fuel inner (some accType) body
  unless b.type == accType do
    reject body.span "the callback of 'reduce' must give a value of the type of the initial value"
  let info : IR.CallbackInfo IR.TyExt :=
    { span := s, result := accType.lean, scope := env.locals.map fun l => (l.name, l.type.lean) }
  return ⟨.listFold xs.value i.value a.name p.name elem.lean b.value info, false, accType⟩

/-- `m.get(k)` and `m.has(k)` on a map. An owned map may be read here, as
`ownedMap?` says. `get` gives `undefined` for a key that the map does not
have, so its value has the type of an optional field. -/
def translateMapMethod (fuel : Nat) (env : Env) (s : Span) (recv : Expr) (op : IR.ExprExt)
    (args : List Expr) : TM Code := do
  let fuel + 1 := fuel | tooDeep
  -- `Number.get` would be a property of the global `Number`, not of a map.
  if recv.namesNumber then reject recv.span "only a map or a set has get and has"
  let [key] := args | reject s "get and has take one key"
  if key matches .arrow .. then reject key.span "a key cannot be an arrow function"
  let o ← translateRecv (translateExpr fuel env none) env recv
  match o.type with
  | .map k v =>
    let kc ← translateExpr fuel env (some k) key
    unless kc.type == k do reject key.span "the key does not have the map's key type"
    if op == .mapHas then return ⟨.ext .mapHas [o.value, kc.value], false, .boolean⟩
    if v.isNullable || v.isOptional then
      reject s "get on a map of nullable values is not supported: the output's none would stand for both null and undefined"
    return ⟨.ext .mapGet [o.value, kc.value], false, .optional v⟩
  -- `s.has(x)` on a set. A set has no `get`.
  | .set t =>
    unless op == .mapHas do reject s "a set has no get; use has"
    let xc ← translateExpr fuel env (some t) key
    unless xc.type == t do reject key.span "the value does not have the set's element type"
    return ⟨.ext .setHas [o.value, xc.value], false, .boolean⟩
  | _ => reject recv.span "only a map or a set has get and has"

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
  let some (.struct ref args) := expected | reject s notStructMessage
  let info ← orReject (ctx.knownStructs.find? (·.ref == ref)) s notStructMessage
  let structName := ref.name
  -- The keys seen so far, and the fields translated so far.
  let (seen, parts) ← props.foldlM (init := (([] : List String), ([] : List (String × IR.Expr))))
    fun (seen, parts) p => do
      let (key, value, span) ← match p with
        | .shorthand ps name => pure (name, Expr.ident ps name, ps)
        | .spread ps _ => reject ps "a spread '...' may only come first in an object literal"
        | .keyValue ps (.ident key) v =>
          if key == "__proto__" then reject ps "'__proto__: v' sets the prototype of the object, not a field"
          else pure (key, v, ps)
        | .keyValue ps _ _ => reject ps "object literal fields must be plain name: value pairs"
      let fieldType ← orReject ((info.fieldsAt args).lookup key) span s!"'{key}' is not a field of {structName}"
      if seen.contains key then reject span s!"'{key}' is set twice"
      -- An optional field holds a `T` when the literal sets it. A key that
      -- holds `undefined` is not the same JS value as no key, and Lean has
      -- one `none` for both, so the literal must leave the field out instead.
      let v ← translateExpr fuel env (some fieldType.unoptional) value
      unless v.type.assignableTo fieldType.unoptional do reject span s!"'{key}' does not have the field's type"
      pure (seen ++ [key], parts ++ [(key, v.value)])
  for (field, type) in info.fieldsAt args do
    unless seen.contains field || type matches .optional _ do
      reject s s!"the object lacks the field '{field}'"
  -- A JS object keeps its keys in the order the literal writes them, and the
  -- caller can see that order, through `Object.keys` or `JSON.stringify`. A
  -- Lean structure has no order, so the literal must use the declared one.
  let declared := (info.fields.map (·.1)).filter seen.contains
  unless seen == declared do
    reject s s!"write the fields in the order that {structName} declares them: {", ".intercalate declared}"
  return ⟨.struct parts ref (Ty.leanList args), false, .struct ref args⟩

/-- `{ ...a, f: e }`, where `a` has an interface: `{ a with f := e }`. The
spread keeps the keys of `a` in their order, and each property after it sets
a field of `a` in its place, so the object keeps the declared order. -/
def translateSpread (fuel : Nat) (env : Env) (s : Span) (base : Expr) (rest : List Property) :
    TM Code := do
  let fuel + 1 := fuel | tooDeep
  let b ← translateExpr fuel env none base
  let some (ref, args) := b.type.structRef?
    | reject s "a spread '...' needs a value of an interface declared in this file, or exported by the files before it"
  let info ← orReject ((← get).knownStructs.find? (·.ref == ref)) base.span
    "a spread '...' needs a value of an interface declared in this file, or exported by the files before it"
  let (_, parts) ← rest.foldlM (init := (([] : List String), ([] : List (String × IR.Expr))))
    fun (seen, parts) p => do
      let (key, value, span) ← match p with
        | .shorthand ps name => pure (name, Expr.ident ps name, ps)
        | .spread ps _ => reject ps "a spread '...' may only come first in an object literal"
        | .keyValue ps (.ident key) v =>
          if key == "__proto__" then reject ps "'__proto__: v' sets the prototype of the object, not a field"
          else pure (key, v, ps)
        | .keyValue ps _ _ => reject ps "object literal fields must be plain name: value pairs"
      let fieldType ← spreadFieldType info.name (info.fieldsAt args) seen span key
      let v ← translateExpr fuel env (some fieldType) value
      unless v.type.assignableTo fieldType do reject span s!"'{key}' does not have the field's type"
      pure (seen ++ [key], parts ++ [(key, v.value)])
  -- Lean does not infer the parameters of the structure, such as the number
  -- model `N`, from `a`, so the update writes its type out, as a literal does.
  return ⟨.ascribe (.structUpdate b.value parts) b.type.lean, false, b.type⟩

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
    reject s "an expression statement must assign a let local, push to an owned array or change an owned map"
  let refuseMap {A : Type} : TM A :=
    reject s ("set, add and delete are allowed only on an owned map or set: a const that the " ++
      "function made with new Map() or new Set()")
  match e with
  -- `m.set(k, v)` and `m.delete(k)` on an owned map: the new map.
  | .call _ (.member _ (.ident _ target) "set") args =>
    let some { binding := .map, type := .map k v, .. } := env.lookup target | refuseMap
    let [key, value] := args | reject s "set takes a key and a value"
    let kc ← translateExpr (← fuelLimit) env (some k) key
    unless kc.type == k do reject key.span "the key does not have the map's key type"
    let vc ← translateExpr (← fuelLimit) env (some v) value
    unless vc.type.assignableTo v do reject value.span "the value does not have the map's value type"
    return (target, .ext .mapSet [.var target, kc.value, vc.value])
  | .call _ (.member _ (.ident _ target) "delete") args =>
    match env.lookup target with
    | some { binding := .map, type := .map k _, .. } =>
      let [key] := args | reject s "delete takes a key"
      let kc ← translateExpr (← fuelLimit) env (some k) key
      unless kc.type == k do reject key.span "the key does not have the map's key type"
      return (target, .ext .mapDelete [.var target, kc.value])
    | some { binding := .map, type := .set t, .. } =>
      let [x] := args | reject s "delete takes a value"
      let xc ← translateExpr (← fuelLimit) env (some t) x
      unless xc.type == t do reject x.span "the value does not have the set's element type"
      return (target, .ext .setDelete [.var target, xc.value])
    | _ => refuseMap
  -- `s.add(x)` on an owned set: the new set.
  | .call _ (.member _ (.ident _ target) "add") args =>
    let some { binding := .map, type := .set t, .. } := env.lookup target | refuseMap
    let [x] := args | reject s "add takes a value"
    let xc ← translateExpr (← fuelLimit) env (some t) x
    unless xc.type == t do reject x.span "the value does not have the set's element type"
    return (target, .ext .setAdd [.var target, xc.value])
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
      -- `s += e` on a string joins strings, as `s = s + e` does.
      if type == .string && bigintOp == .add then
        let c ← concatOperands s ⟨.var name, false, .string⟩ v
        return (name, c.value)
      unless type == .bigint && v.type == .bigint do
        reject s "arithmetic needs two bigints or two numbers"
      return (name, .update bigintOp name v.value)
  | _ => refuse

/-- The type that an annotation such as `: T` names, if there is one. -/
def translateAnnotation : Option TypeExpr → TM (Option Ty)
  | some annotation => some <$> translateType annotation
  | none => pure none

/-- `const x = f(a)` or `let x = f(a)`, where `f` can throw: the call of the
output, and the scope after the declaration. The output passes the error of
the call on. -/
def translateBindHead (env : Env) (s : Span) (d : VarDecl) (cs sp : Span) (name : String)
    (args : List Expr) : TM (DeclRef × List IR.Expr × Env) := do
  let code ← translateCall (← fuelLimit) env cs (.ident sp name) args true
  let declared ← translateAnnotation d.type
  unless declared.all (· == code.type) do reject s "the call must have the declared type"
  let .call ref outs := code.code | reject s "unsupported call"
  let env' ← declare env s d.name (if d.kind == .const then .const else .«let») code.type
  return (ref, outs, env')

/-- `return f(a)`, where `f` can throw: the call of the output. The output
passes the error of the call on. -/
def translateReturnCall (env : Env) (s : Span) (cs sp : Span) (name : String)
    (args : List Expr) : TM (DeclRef × List IR.Expr) := do
  let returnType := (← get).returnType
  let code ← translateCall (← fuelLimit) env cs (.ident sp name) args true
  unless code.type == returnType do reject s "the call must have the function's return type"
  let .call ref outs := code.code | reject s "unsupported call"
  return (ref, outs)

/-- The places of a pattern on a tuple `v` of `size` elements, from the
element `i` on: each name with the type of its element and the code that
reads it. -/
def tuplePlaces (v : IR.Expr) (size : Nat) : List (Option String) → List Ty → Nat →
    List (String × Ty × IR.Expr)
  | x :: xs, t :: ts, i => (x.map fun n => (n, t, .proj v i size)).toList ++ tuplePlaces v size xs ts (i + 1)
  | _, _, _ => []

/-- The places of a pattern on the list `li` of the values that iterating
gives, from the position `i` on: each name, as the optional value at its
position, which is `undefined` past the end, as `xs[i]` is. -/
def listPlaces (elem : Ty) (li : IR.Expr) : List (Option String) → Nat → List (String × Ty × IR.Expr)
  | [], _ => []
  | x :: xs, i =>
    (x.map fun n => (n, .optional elem, .ascribe (.ext (.indexLit i) [li]) (Ty.optional elem).lean)).toList ++
      listPlaces elem li xs (i + 1)

/-- What `const [a, , b, ...r] = e` binds, where `c` is the code of `e`: each
name, with its type and the code that reads its value. A tuple gives its
elements. An array, a set or a map gives the values that a loop over it
visits, each optional, and the rest is the list of the values after the
places. -/
def patternReads (s : Span) (p : ArrayPattern) (c : Code) : TM (List (String × Ty × IR.Expr)) := do
  match c.type.tupleElems? with
  | some tys =>
    if p.rest.isSome then reject s "a rest element on a tuple is not supported; destructure an array"
    unless p.elems.length ≤ tys.length do reject s s!"the tuple has only {tys.length} elements"
    return tuplePlaces c.value tys.length p.elems tys 0
  | none =>
    let (elem, li) ← orReject (loopOver c) s "destructuring needs a tuple, an array, a set or a map"
    -- The output has one `none` for `undefined` and `null`.
    if elem.isMaybe then reject s "destructuring an array of nullable values could give null or undefined"
    return listPlaces elem li p.elems 0 ++
      (p.rest.map fun r => (r, .array elem, .ext (.slice p.elems.length none) [li])).toList

/-- The type that an annotation declares, if any. -/
def declaredType : Option TypeExpr → TM (Option Ty)
  | some annotation => some <$> translateType annotation
  | none => pure none

/-- The type of a value: the declared one, which the value's type must fit,
or else the value's own. -/
def fitDeclared (s : Span) (declared : Option Ty) (code : Code) : TM Ty :=
  match declared with
  | some t => if code.type.assignableTo t then pure t else reject s "the value does not have the declared type"
  | none => pure code.type

/-- The pattern names every element of the tuple type `t`, in order. -/
def exactTuple (p : ArrayPattern) : Ty → Bool
  | .tuple tys => p.rest.isNone && p.elems.all Option.isSome && p.elems.length == tys.length
  | _ => false

/-- The output of a pattern whose names `reads` read the value `value` of type
`t`, then `rest`: one `let` for one name, and one `let (a, b) := …` for more,
which binds the tuple itself when the pattern names each of its elements. -/
def destructureBody (p : ArrayPattern) (t : Ty) (value : IR.Expr) (reads : List (String × Ty × IR.Expr))
    (rest : IR.Body) : Option IR.Body :=
  match reads with
  | [] => none
  | [(n, _, e)] => some (.let n e rest)
  | _ => some (.letTuple (reads.map (·.1))
      (if exactTuple p t then value else .tuple (reads.map (·.2.2))) rest)

/-- Declare each name of a pattern, in order. -/
def declarePlaces (s : Span) (binding : Binding) : Env → List (String × Ty × IR.Expr) → TM Env
  | env, [] => pure env
  | env, (n, t, _) :: ps => do declarePlaces s binding (← declare env s n binding t) ps

/-- `const [a, b] = e`, then the statements after it, which `k` translates in
the scope with the names. The output reads `e` once: a tuple with as many
names as elements binds them all with `let (a, b) := e`, and any other
pattern binds `let (a, b) := (e.1, e.2.1)` or `(xs[0]?, xs[1]?)`. `tr`
translates an expression in the scope before the names. -/
def translateDestructure (tr : Option Ty → Expr → TM Code) (k : Env → TM IR.Body) (env : Env)
    (s : Span) (kind : VarKind) (p : ArrayPattern) (type : Option TypeExpr) (init : Expr) : TM IR.Body := do
  let declared ← declaredType type
  let code ← tr declared init
  let t ← fitDeclared s declared code
  let reads ← patternReads s p ⟨withType code.value t code.type, false, t⟩
  let env' ← declarePlaces s (if kind == .const then .const else .«let») env reads
  let rest ← k env'
  orReject (destructureBody p t (withType code.value t code.type) reads rest) s "a pattern must declare a name"

/-- `for (const [k, v] of xs) body`, then the statements after it, as
`translateLoop` translates a loop. The fold binds each element to the first
name of the pattern, and the body starts by binding the names of the pattern
as `const [k, v] = element` does, which hides that first binding. `items`
translates the iterable, `kBody` the body in its scope and `kRest` the
statements after the loop. -/
def translateForOfPattern (items : TM Code) (kBody : Env → Tail → List Stmt → TM IR.Body)
    (kRest : TM IR.Body) (env : Env) (s : Span) (kind : VarKind) (p : ArrayPattern) (iterable : Expr)
    (body : Stmt) (tail : Tail) : TM IR.Body := do
  unless kind == .const do reject s "a loop must be 'for (const [a, b] of xs)'"
  let bodyStatements := blockStatements body
  let returns := bodyStatements.any (containsJump false false)
  if returns && !tail.isRet then
    reject s "a loop body may return only where the statements after the loop end in a return"
  let breaks := bodyStatements.any (containsJump true false)
  let names := changedNames bodyStatements env
  if names.isEmpty && !returns then reject s "a loop must change a local or return"
  let (elemType, loopItems) ← loopItems iterable body (← items)
  let x ← orReject p.names.head? s "a pattern must declare a name"
  let reads ← patternReads s p ⟨.var x, false, elemType⟩
  let bodyEnv ← declarePlaces s .const env reads
  let bodyOut ← kBody bodyEnv (.loop names breaks returns) bodyStatements
  let step ← orReject (destructureBody p elemType (.var x) reads bodyOut) s "a pattern must declare a name"
  let returnType := (← get).returnType
  let throws := (← get).throws
  let info : IR.LoopInfo :=
    { span := s, elem := elemType.lean,
      stateTypes := names.filterMap fun n => (env.lookup n).map (·.type.lean),
      scope := (env.locals.filter fun l => !names.contains l.name).map fun l => (l.name, l.type.lean),
      breaks, returns := if returns then some (leanResult throws returnType) else none }
  return .fold names x step loopItems (← kRest) info

/-- The head of a loop that the output runs as a fold: `for (kind x of xs)`,
or a counted `for` with its declaration, its test and its update. -/
inductive LoopHead where
  | forOf (kind : VarKind) (element : String) (iterable : Expr)
  | counted (init : Option VarDecl) (test update : Option Expr)

/-- The loop with the head `h` and the body `body`. -/
def LoopHead.stmt (s : Span) (body : Stmt) : LoopHead → Stmt
  | .forOf kind element iterable => .forOfStmt s kind element iterable body
  | .counted init test update => .forStmt s init test update body

/-- Why the translator refuses a counted loop of another shape. -/
def countedReason : String :=
  "a counted loop must be 'for (let i = a; i < b; i++)', with '++i' or 'i += 1' as the update"

/-- What `for (let i = k; i < b; i++)` visits: the name `i`, the type of its
values and the list of them in the output, `JSNumber.countUp k b`. That list
is `k`, then each integer after it that is less than `b`. The start `k` must
be an integer literal, which the interpreter reads as the translation does. -/
def countedHead (env : Env) (s : Span) (body : Stmt) (init : Option VarDecl) (test update : Option Expr) :
    TM (String × Ty × IR.Expr) :=
  match init, test, update with
  | some ⟨.let, name, type, some start⟩, some (.binary _ .lt (.ident _ n) bound), some update => do
    unless n == name && update.incrementsName name do reject s countedReason
    unless type.all (· matches .keyword _ "number") do reject s "the variable of a counted loop must be a number"
    -- JS reads the bound again before each run of the body, and the output
    -- reads it once.
    if Stmt.countedChanges name bound body then
      reject s "the body of a counted loop may not assign its variable or change what its bound reads"
    let some k := Eval.countStart? start
      | reject start.span "the start of a counted loop must be an integer literal, such as 0"
    let b ← translateExpr (← fuelLimit) env (some .number) bound
    unless b.type == .number do reject bound.span "the bound of a counted loop must be a number"
    return (name, .number, .ext (.countUp k) [b.value])
  | _, _, _ => reject s countedReason

/-- What the loop with the head `h` visits: the name of its variable, the type
of the values and the list of them in the output. `for (const x of xs)`
visits the values of `xs`. -/
def loopHead (env : Env) (s : Span) (body : Stmt) : LoopHead → TM (String × Ty × IR.Expr)
  | .forOf kind element iterable => do
    unless kind == .const do reject s "a loop must be 'for (const x of xs)'"
    -- An owned map or set may be the iterable, as long as the body does not
    -- change it: a JS loop would visit the values that the body adds.
    let items ← translateRecv (translateExpr (← fuelLimit) env none) env iterable
    let (elemType, items) ← loopItems iterable body items
    return (element, elemType, items)
  | .counted init test update => countedHead env s body init test update

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
    | .loop names b r => return stepEnd names b r
    | .cont .. =>
      let ctx ← get
      throw s!"{ctx.file}: a branch of '{ctx.currentFunction}' that must end in continue or break can end without one"
  | stmt :: rest =>
    match stmt with
    | .returnStmt s value =>
      let ([], some v, true) := (rest, value, tail.canReturn)
        | reject s "return must be the last statement of a function or a loop body and carry a value"
      match throwingCall? env.functions v with
      -- `return f(x)`, where `f` can throw: the output passes its error on.
      | some (cs, sp, name, args) =>
        let (ref, outs) ← translateReturnCall env s cs sp name args
        return .bind "r" ref outs (tail.returnBody (IR.Expr.pure (.var "r")))
      | none =>
        modify fun c => { c with returning := true }
        let returnType := (← get).returnType
        let code ← translateExpr (← fuelLimit) env (some returnType) v
        unless code.type.assignableTo returnType do
          reject v.span "the value does not have the function's return type"
        modify fun c => { c with returning := false }
        return tail.returnBody (if (← get).throws then IR.Expr.pure code.value else code.value)
    | .varDecl s d => translateVariable fuel env s d rest tail
    | .destructure s kind p type init =>
      if stmt.constAssignedIn rest then
        reject s "a name of the pattern is a const, and a later statement assigns it; declare it with let"
      if (throwingCall? env.functions init).isSome then
        reject init.span "a pattern may not take the value of a call that can throw; declare a const for the call first"
      translateDestructure (fun exp e => do translateExpr (← fuelLimit) env exp e)
        (fun env' => translateStatements fuel env' tail rest) env s kind p type init
    | .exprStmt s e =>
      let (name, update) ← translateUpdate env s e
      return .let name update (← translateStatements fuel env tail rest)
    | .ifStmt s test thenBranch elseBranch =>
      translateIf fuel env s test thenBranch elseBranch rest tail
    | .forOfStmt s kind name iterable body =>
      translateLoop fuel env s (.forOf kind name iterable) body rest tail
    | .forOfPattern s kind p iterable body =>
      translateForOfPattern (do translateRecv (translateExpr (← fuelLimit) env none) env iterable)
        (fun env' t ss => translateStatements fuel env' t ss) (translateStatements fuel env tail rest)
        env s kind p iterable body tail
    | .forStmt s init test update body =>
      translateLoop fuel env s (.counted init test update) body rest tail
    | .switchStmt s disc clauses => translateSwitch fuel env s disc clauses rest tail
    -- `throw new Error(m)` ends the function with the error, from a loop
    -- body or a branch as well: the output runs those in the `Except` monad.
    | .throwStmt s value =>
      unless rest.isEmpty do reject s "code after throw is unreachable"
      let .new _ "Error" [] [msg] := value
        | reject value.span "tolean supports only 'throw new Error(message)'"
      if env.has "Error" then reject value.span "a local named Error hides the global"
      let code ← translateExpr (← fuelLimit) env (some .string) msg
      unless code.type == .string do reject msg.span "the message of an Error must be a string"
      return .throw (IR.Expr.error code.value)
    -- `continue` ends one run of the loop body with the state as it is.
    | .continueStmt s =>
      let some next := tail.continues
        | reject s "continue may only end a loop body, or a branch of an if at the top of one"
      unless rest.isEmpty do reject s "code after continue is unreachable"
      return next
    -- `break` ends the loop with the state as it is. A `break` that ends a
    -- clause of a `switch` never comes here.
    | .breakStmt s =>
      let some done := tail.breaks
        | reject s "break may only end a loop body, a branch of an if at the top of one, or a clause of a switch"
      unless rest.isEmpty do reject s "code after break is unreachable"
      return done
    | _ => reject stmt.span "unsupported statement"

def translateVariable (fuel : Nat) (env : Env) (s : Span) (d : VarDecl) (rest : List Stmt)
    (tail : Tail) : TM IR.Body := do
  let fuel + 1 := fuel | tooDeep
  if (Stmt.varDecl s d).constAssignedIn rest then
    reject s s!"'{d.name}' is a const, and a later statement assigns it; declare it with let"
  let init ← orReject d.init s "declare one const or let identifier with an initializer"
  match throwingCall? env.functions init with
  -- `const x = f(a)`, where `f` can throw: the output passes its error on, and
  -- binds `x` to the value otherwise.
  | some (cs, sp, name, args) =>
    let (ref, outs, env') ← translateBindHead env s d cs sp name args
    return .bind d.name ref outs (← translateStatements fuel env' tail rest)
  | none =>
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
        let .array sa elems := init | unreachable!
        if elems.any (·.spreadArg?.isSome) then
          -- `const xs: Array<T> = [...ys, y]` copies `ys`, so the function
          -- owns the new array as it owns any other literal.
          let code ← translateArray (← fuelLimit) env (some type) sa elems
          let env' ← declare env s d.name .array type
          return .let d.name code.value (← translateStatements fuel env' tail rest)
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
    let env' ← declare env s d.name (varBinding d.kind init) type
    return .let d.name (withType code.value type code.type) (← translateStatements fuel env' tail rest)

def translateIf (fuel : Nat) (env : Env) (s : Span) (test : Expr) (thenBranch : Stmt)
    (elseBranch : Option Stmt) (rest : List Stmt) (tail : Tail) : TM IR.Body := do
  let fuel + 1 := fuel | tooDeep
  let thenStatements := blockStatements thenBranch
  let elseStatements := (elseBranch.map blockStatements).getD []
  -- `if (x === null)` and `if (x !== null)`, or `x === undefined` and
  -- `x !== undefined` on an optional value: TypeScript narrows `x` in each
  -- branch, so Lean matches on `x` and binds it to the value. Where an
  -- optional `x` is `undefined`, the subset has no type for it alone, so it
  -- keeps its optional type, and `x ?? d` still reads it.
  let nullTest := noneTestOf env test
  -- `if (x.kind === 'circle')`: TypeScript narrows `x` to the member in one
  -- branch and to the other members in the other, so Lean matches on the
  -- constructor.
  let tagTest := tagTestOf env test
  let noneType (value : Ty) (optional : Bool) : Ty := if optional then .optional value else .null
  let (envTrue, envFalse) := match nullTest, tagTest with
    | some (name, true, value, o), _ => (env.narrow name (noneType value o), env.narrow name value)
    | some (name, false, value, o), _ => (env.narrow name value, env.narrow name (noneType value o))
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
    | some (name, isNullTest, _, optional), _ =>
      return if isNullTest then .matchNull name optional whenTrue whenFalse
        else .matchNull name optional whenFalse whenTrue
    | none, some t =>
      let (whenTag, whenOther) := if t.isEq then (whenTrue, whenFalse) else (whenFalse, whenTrue)
      -- Where more than one member is left, Lean matches the others with a
      -- catch-all. A further test of the local is exhaustive only as more
      -- arms of the same `match`, so it must come first there.
      if t.other.isNone && !(nestsTag t.name whenOther) then
        reject s ("where more than one member of the union is left, a further test of its tag " ++
          "must come right after, as in a chain of 'if (x.kind === 'a') return …'")
      return .matchTag t.name t.ref t.field t.tag t.other whenTag whenOther
  -- `if (c) return …;` in a function body, or `if (c) continue;` in a loop
  -- body: the statements after the `if` run only when `c` does not hold, so
  -- they join its other branch.
  if let some thenTail := earlyTail tail thenStatements then
    if elseBranch.isSome && !rest.isEmpty then
      reject s thenTail.afterEarlyReason
    let whenTrue ← translateStatements fuel envTrue thenTail thenStatements
    let whenFalse ← translateStatements fuel envFalse tail (elseStatements ++ rest)
    return (← branch whenTrue whenFalse)
  if (thenStatements ++ elseStatements).any (containsJump true true) then
    reject s "a branch that does not always return may not return, break or continue"
  let names := changedNames (thenStatements ++ elseStatements) env
  if names.isEmpty then reject s "an if without a return must change a local"
  let tested := match nullTest, tagTest with
    | some (name, _, _, _), _ => some name
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
    if checksNever sw.name [(none, body)] then reject s (neverLeftReason sw.name tags)
    else if !rest.isEmpty then reject s "code after a switch with a default is unreachable"
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
            else if !(more.isEmpty || checksNever sw.name more) then
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
  | [(none, body)] =>
    if checksNever sw.name [(none, body)] then reject s (neverLeftReason sw.name tags)
    else translateStateClause fuel env s names true body
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
            else if !(more.isEmpty || checksNever sw.name more) then
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
  else if anyContainsJump true true (dropBreak body) then
    reject s "a clause of a switch that ends in break may not return, break or continue before its end"
  else translateStatements fuel env (.state names) (dropBreak body)

def translateLoop (fuel : Nat) (env : Env) (s : Span) (head : LoopHead) (body : Stmt)
    (rest : List Stmt) (tail : Tail) : TM IR.Body := do
  let fuel + 1 := fuel | tooDeep
  let bodyStatements := blockStatements body
  -- A `return` ends the function, so the statements after the loop must end
  -- it too. A `break` of this loop, and not of a loop inside it, or a
  -- `return`, makes it a `forIn`.
  let returns := bodyStatements.any (containsJump false false)
  if returns && !tail.isRet then
    reject s "a loop body may return only where the statements after the loop end in a return"
  let breaks := bodyStatements.any (containsJump true false)
  let names := changedNames bodyStatements env
  if names.isEmpty && !returns then reject s "a loop must change a local or return"
  let (element, elemType, loopItems) ← loopHead env s body head
  let bodyEnv ← declare env s element .const elemType
  let bodyOut ← translateStatements fuel bodyEnv (.loop names breaks returns) bodyStatements
  let returnType := (← get).returnType
  let throws := (← get).throws
  let info : IR.LoopInfo :=
    { span := s, elem := elemType.lean,
      stateTypes := names.filterMap fun n => (env.lookup n).map (·.type.lean),
      scope := (env.locals.filter fun l => !names.contains l.name).map fun l => (l.name, l.type.lean),
      breaks, returns := if returns then some (leanResult throws returnType) else none }
  return .fold names element bodyOut loopItems (← translateStatements fuel env tail rest) info

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

/-- The file has declared or imported `name`. -/
def Ctx.taken (ctx : Ctx) (name : String) : Bool :=
  ctx.structs.any (·.name == name) || ctx.aliases.any (·.name == name) ||
    ctx.enums.any (·.name == name) || ctx.unions.any (·.name == name) ||
    ctx.functions.any (·.name == name)

def declareTopLevel (s : Span) (name : String) : TM Unit := do
  let ctx ← get
  if ctx.taken name then
    reject s s!"'{name}' is declared twice"
  -- A declaration of the module hides the global of the same name, and the
  -- subset reads these names as the globals.
  if isGlobalName name then
    reject s s!"'{name}' would hide the global {name}; choose another name"

mutual

/-- `t` names the type `name`, as a type parameter does in the types that use
it. -/
def typeNames (name : String) : TypeExpr → Bool
  | .ref _ n args => n == name || typesName name args
  | .array _ e | .paren _ e => typeNames name e
  | .union _ members | .tuple _ _ members => typesName name members
  | _ => false

def typesName (name : String) : List TypeExpr → Bool
  | [] => false
  | t :: ts => typeNames name t || typesName name ts

end

/-- The type parameters `vs` of a declaration, after the ones in `seen`: each
one a fresh name. A function's must each be `named` by a parameter's type, so
that the arguments of a call fix it. -/
def checkTypeParams (s : Span) (named : String → Bool) (seen : List String) : List String → TM Unit
  | [] => return ()
  | v :: vs => do
    let _ ← checkName s v
    if seen.contains v then reject s s!"the type parameter '{v}' is declared twice"
    if (← get).taken v then
      reject s s!"the type parameter '{v}' would hide the type or function {v} in Lean; choose another name"
    unless named v do
      reject s s!"no parameter's type names the type parameter '{v}', so a call could not fix it"
    checkTypeParams s named (seen ++ [v]) vs

mutual

/-- Every use of the interface `self` in the type passes it `args`. -/
def Ty.namesSelfWith (self : DeclRef) (args : List Ty) : Ty → Bool
  | .struct r rs => (r != self || rs == args) && Ty.namesSelfWithList self args rs
  | .nullable t | .optional t | .array t => t.namesSelfWith self args
  | .tuple ts => Ty.namesSelfWithList self args ts
  | _ => true

def Ty.namesSelfWithList (self : DeclRef) (args : List Ty) : List Ty → Bool
  | [] => true
  | t :: ts => t.namesSelfWith self args && Ty.namesSelfWithList self args ts

end

mutual

/-- The type names a declaration `name` of the file `file`, which the output
writes by that name alone. -/
def Ty.namesDecl (file name : String) : Ty → Bool
  | .struct r rs => (r.file == file && r.name == name) || Ty.namesDeclList file name rs
  | .enum r | .tagged r _ => r.file == file && r.name == name
  | .nullable t | .optional t | .array t => t.namesDecl file name
  | .tuple ts => Ty.namesDeclList file name ts
  | _ => false

def Ty.namesDeclList (file name : String) : List Ty → Bool
  | [] => false
  | t :: ts => t.namesDecl file name || Ty.namesDeclList file name ts

end

def translateInterface (s : Span) (exported : Bool) (name : String) (typeParams : List String)
    (fields : List Field) : TM IR.Decl := do
  let name ← checkName s name
  declareTopLevel s name
  checkTypeParams s (fun _ => true) [] typeParams
  modify fun c => { c with typeParams }
  -- A field may name the interface itself, as a tree node names its
  -- children, so the interface is in scope while its fields translate. Lean
  -- reads such a structure as a nested inductive type.
  let infos ← isolated do
    modify fun c => { c with structs := c.structs ++ [{ file := c.file, name, exported, typeParams, fields := [] }] }
    fields.foldlM (init := ([] : List (String × Ty))) fun infos f => do
      unless f.readonly do
        reject f.span "interface fields must be readonly and typed"
      let field ← checkName f.span f.name
      if infos.any (·.1 == field) then reject f.span s!"'{field}' is declared twice"
      -- A Lean structure's fields are in scope in the types of the fields after
      -- them, so a field may not hide a type parameter.
      if typeParams.contains field then
        reject f.span s!"'{field}' would hide the type parameter {field} in Lean; choose another name"
      -- A field of one string literal type is a tag, which a union reads.
      let type ← match f.type with
        | .literal _ (.string v) =>
          if f.optional then reject f.span "a tag field may not be optional" else pure (Ty.literal v)
        | t => translateType t
      -- Lean's kernel accepts a structure that refers to itself only with
      -- its own type parameters, in order.
      unless type.namesSelfWith ⟨(← get).file, name⟩ (typeParams.map .param) do
        reject f.span s!"'{name}' may refer to itself only with its own type parameters, in order"
      -- The same holds for a field that has the name of a type, such as the
      -- interface itself, which the type of a later field names.
      let file := (← get).file
      if let some (hidden, _) := infos.find? fun (g, _) => type.namesDecl file g then
        reject f.span s!"the field '{hidden}' before this one would hide the type {hidden} in Lean; rename the field"
      -- `f?: T`: an object may leave the field out, and a read of it then gives
      -- `undefined`. An object without the field would inherit a property of
      -- `Object.prototype` of the same name.
      let type ← if !f.optional then pure type
        else if type.isNullable then reject f.span "an optional field may not also be nullable"
        else if Eval.objectPrototypeNames.contains field then
          reject f.span s!"an optional field may not be named '{field}', because an object without it has Object.prototype.{field}"
        else pure (Ty.optional type)
      pure (infos ++ [(field, type)])
  modify fun c => { c with
    typeParams := [], structs := c.structs ++ [{ file := c.file, name, exported, typeParams, fields := infos }] }
  return .struct name typeParams (infos.map fun (field, type) => (field, type.lean))

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

/-- Why the subset refuses the members of a string enum, and where: an enum
needs a member, two members may not have one name, and a member may not have
the name of a property of `Object.prototype`. The object of the enum is an
ordinary object, and setting `__proto__` on it sets its prototype instead of
a property. Each string must also name a constructor, as for a literal
union, and two members may not have one string, because the output names a
constructor by its string. -/
def enumRefusal (s : Span) (members : List EnumMember) : Option (Span × String) :=
  if members.isEmpty then some (s, "an enum needs a member")
  else match members.findSome? fun m =>
      if (members.filter (·.name == m.name)).length > 1 then some (m.span, s!"'{m.name}' is declared twice")
      else if Eval.objectPrototypeNames.contains m.name then
        some (m.span, s!"a member may not be named '{m.name}', the name of a property of Object.prototype")
      else if !memberOK m.value then
        some (m.span, s!"'{m.value}' cannot name a Lean constructor; a string enum needs strings such as 'open'")
      else if (members.filter (·.value == m.value)).length > 1 then
        some (m.span, s!"two members have the string '{m.value}'")
      else none with
    | some r => some r
    | none => (badMember (members.map (·.value))).map (s, ·)

/-- `enum T { A = 'a', B = 'b' }`. TypeScript compiles it to an object with a
property for each member, whose value is the member's string, so `T.A` is
`'a'`. The output declares the inductive type of the literal union
`'a' | 'b'`, and `T.A` becomes its constructor `T.a`. -/
def translateStringEnum (s : Span) (exported : Bool) (name : String) (members : List EnumMember) :
    TM IR.Decl := do
  let name ← checkName s name
  declareTopLevel s name
  match enumRefusal s members with
  | some (sp, reason) => reject sp reason
  | none =>
    let pairs := members.map fun m => (m.name, m.value)
    modify fun c => { c with
      enums := c.enums ++ [{ file := c.file, name, exported, members := pairs.map (·.2), named := some pairs }],
      enumValues := c.enumValues ++ [{ name, ref := ⟨c.file, name⟩, members := pairs }] }
    return .enum name (pairs.map (·.2))

/-- The interfaces of a union `A | B` of interfaces that the file declares or
imports, or none when a member is something else. -/
def unionMembers (structs : List StructInfo) : TypeExpr → Option (List StructInfo)
  | .union _ members => members.mapM fun
    | .ref _ n [] => structs.find? fun i => i.name == n && i.typeParams.isEmpty
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
    declareUnion s exported name (some field) (tags.zip (members.map (.struct ·.ref [])))

/-- `type T = string | bigint`, a union of primitive types. Each constructor
holds a value of its type, and its tag is what `typeof` gives for that value,
so `typeof x === 'string'` tests it. In JS and in the interpreter a value is
still the primitive value. -/
def translatePrimitiveUnion (s : Span) (exported : Bool) (name : String) (members : List String) :
    TM IR.Decl := do
  if members.contains "bigint" then requireFeature s .bigint
  declareUnion s exported name none (members.filterMap fun k => (primitiveType? k).map (k, ·))

/-- `t` is a union of names only, such as `A | B`, which a type alias declares
as a union of interfaces. -/
def isNameUnion : TypeExpr → Bool
  | .union _ members => members.all (· matches .ref _ _ [])
  | _ => false

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
  return .struct name [] (fields.map fun (field, type) => (field, type.lean))

/-- `type T = U`. The translator writes the type of `U` wherever the source
names `T`, so a type alias changes no code. The output declares it as an
`abbrev`, for the claims about the code to use. An alias must come before its
uses, as an interface must. -/
def translateAlias (s : Span) (exported : Bool) (name : String) (typeParams : List String) (type : TypeExpr) :
    TM IR.Decl := do
  let name ← checkName s name
  declareTopLevel s name
  -- A union, or a Record, becomes a type of its own, which takes no type
  -- parameters.
  if !typeParams.isEmpty && ((stringLiterals type).isSome || (primitiveMembers type).isSome ||
      isNameUnion type || (recordArgs type).isSome) then
    reject s "a union of string literals, primitive types or interfaces, or a Record, may not have type parameters"
  if let some members := stringLiterals type then
    return ← translateEnum s exported name members
  if let some members := unionMembers (← get).structs type then
    return ← translateUnion s exported name members
  if let some members := primitiveMembers type then
    return ← translatePrimitiveUnion s exported name members
  if let some (key, value) := recordArgs type then
    return ← translateRecord exported name key value
  checkTypeParams s (fun _ => true) [] typeParams
  modify fun c => { c with typeParams }
  let ty ← isolated (translateType type)
  modify fun c => { c with
    typeParams := [], aliases := c.aliases ++ [{ file := c.file, name, exported, typeParams, type := ty }] }
  return .alias name typeParams ty.lean

/-- The type of a parameter of type `type`, after parameters of the types
`before`: `T`, or the optional `T` of `x?: T`, which is `undefined` when a
call leaves it out. TypeScript lets no required parameter follow an optional
one. The output has one `none` for both `undefined` and `null`, so an
optional parameter may not be nullable too. -/
def paramType (span : Span) (optional : Bool) (type : TypeExpr) (before : List Ty) : TM Ty := do
  let ty ← translateType type
  if !optional then
    if before.any (· matches .optional _) then
      reject span "a required parameter may not follow an optional one"
    return ty
  if ty.isNullable || ty == .null then reject span "an optional parameter may not also be nullable"
  return .optional ty

def translateFunction (thr : String → Bool) (s : Span) (exported : Bool) (name : String)
    (typeParams : List String) (params : List Param) (returnType : Option TypeExpr) (body : Stmt) :
    TM IR.Decl := do
  let some returnType := returnType
    | reject s "functions must be named, typed and synchronous"
  -- Each call that can throw moves out of its statement into a `const` of
  -- its own, as the model runs the body (`Eval.Stmt.hoisted`). So the body
  -- translated here is the body the model runs, and a call of a function
  -- that can throw meets the translator only as the whole value of a
  -- declaration or a `return`, or in a place that JS may not evaluate.
  let body := Eval.Stmt.hoisted thr body
  let name ← checkName s name
  declareTopLevel s name
  checkTypeParams s (fun v => params.any fun p => (p.type.map (typeNames v)).getD false) [] typeParams
  modify fun c => { c with typeParams }
  -- The scope of the body, and the parameters in Lean and as types.
  let ctx ← get
  let start : Env := { functions := ctx.functions, unions := ctx.knownUnions, enums := ctx.enumValues }
  let (env, leanParams, types) ← isolated <| params.foldlM
    (init := (start, ([] : List (String × IR.Ty)), ([] : List Ty)))
    fun (env, leanParams, types) p => do
      let type ← orReject p.type p.span "parameters must be plain, typed identifiers"
      let paramName ← checkLocalName p.span p.name
      if env.has paramName then reject p.span s!"'{paramName}' is declared twice"
      let ty ← paramType p.span p.optional type types
      pure (env.add { name := paramName, binding := .param, type := ty },
        leanParams ++ [(paramName, ty.lean)], types ++ [ty])
  let ret ← isolated (translateType returnType)
  let throws := stmtsThrow ctx.functions (blockStatements body)
  modify fun c => { c with currentFunction := name, returnType := ret, throws }
  -- The body may call the function itself. Lean must see that the calls
  -- end, so each must pass a part of one parameter, the same one in every
  -- call.
  let self : FnInfo := { file := ctx.file, name, exported, typeParams, params := types, ret, throws }
  let out ← isolated (translateStatements (← fuelLimit) { env with functions := env.functions ++ [self] } .ret
    (blockStatements body))
  if out.calls self.ref && (out.decreasingParam? self.ref leanParams).isNone then
    reject s ("a function may call itself only on a part of one of its parameters, the same one in " ++
      "every call: a field of it, a value that a test narrows it to, or an element of an array in it")
  -- The spec gives no value for a function that fails this test, because its
  -- model of a collection as a value would not be the JS meaning.
  if !Stmt.ownsChanges (params.map (·.name)) body then
    reject s ("a function may change only an array, a map or a set that it makes in a const, under a " ++
      "name that no other variable of it has, and may hand it on only in its return value")
  modify fun c => { c with typeParams := [], throws := false, functions := c.functions ++ [self] }
  return .function name leanParams (leanResult throws ret) out

/-! ### The number model -/

mutual

def typeUsesNumber : TypeExpr → Bool
  | .keyword _ name => name == "number"
  | .literal _ (.number _) => true
  | .ref _ name args => isNumberName name || typesUseNumber args
  | .array _ e | .paren _ e => typeUsesNumber e
  | .union _ members | .tuple _ _ members => typesUseNumber members
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
  -- `xs.length`, `s.length`, `s.indexOf(p)` and `xs.findIndex(…)` give a
  -- number, and so does `m.size`. The source does not say whether `xs` is an
  -- array, `s` a string or `m` a map, so a field with one of these names
  -- makes the file generic too, which costs nothing.
  | .member _ obj name | .optMember _ obj name =>
    isNumberName name || name == "length" || name == "indexOf" || name == "findIndex" ||
      name == "size" || exprUsesNumber obj
  | .object _ props => propsUseNumber props
  | .array _ es => exprsUseNumber es
  | .call _ f args => exprUsesNumber f || exprsUseNumber args
  | .paren _ e | .unary _ _ e | .prefix _ _ e | .postfix _ _ e => exprUsesNumber e
  | .asConst _ e | .spread _ e => exprUsesNumber e
  | .satisfies _ e t => exprUsesNumber e || typeUsesNumber t
  -- The index of a tuple, `t[0]`, is a position in the output, not a number.
  | .index _ a (.number ..) => exprUsesNumber a
  | .index _ a b | .binary _ _ a b | .assign _ _ a b => exprUsesNumber a || exprUsesNumber b
  | .cond _ a b c => exprUsesNumber a || exprUsesNumber b || exprUsesNumber c
  -- `new Map<bigint, number>()` names `number` only in its type arguments.
  | .new _ callee typeArgs args => isNumberName callee || typesUseNumber typeArgs || exprsUseNumber args
  -- The index that `map` passes to a second parameter is a number.
  | .arrow _ _ ps body =>
    ps.length ≥ 2 ||
    ps.any (fun p => isNumberName p.name || (p.type.map typeUsesNumber).getD false) ||
      exprUsesNumber body
  | _ => false

def exprsUseNumber : List Expr → Bool
  | [] => false
  | e :: es => exprUsesNumber e || exprsUseNumber es

def propsUseNumber : List Property → Bool
  | [] => false
  | .shorthand _ name :: ps => isNumberName name || propsUseNumber ps
  | .keyValue _ key value :: ps => (keyUsesNumber key || exprUsesNumber value) || propsUseNumber ps
  | .spread _ value :: ps => exprUsesNumber value || propsUseNumber ps

end

def varUsesNumber (d : VarDecl) : Bool :=
  isNumberName d.name || (d.type.map typeUsesNumber).getD false ||
    (d.init.map exprUsesNumber).getD false

mutual

def stmtUsesNumber : Stmt → Bool
  | .varDecl _ d => varUsesNumber d
  | .destructure _ _ p type init =>
    p.names.any isNumberName || (type.map typeUsesNumber).getD false || exprUsesNumber init
  | .exprStmt _ e => exprUsesNumber e
  | .returnStmt _ v => (v.map exprUsesNumber).getD false
  | .throwStmt _ e => exprUsesNumber e
  | .ifStmt _ test t (some e) => exprUsesNumber test || stmtUsesNumber t || stmtUsesNumber e
  | .ifStmt _ test t none => exprUsesNumber test || stmtUsesNumber t
  | .forOfStmt _ _ name iterable body =>
    isNumberName name || exprUsesNumber iterable || stmtUsesNumber body
  | .forOfPattern _ _ p iterable body =>
    p.names.any isNumberName || exprUsesNumber iterable || stmtUsesNumber body
  | .forStmt _ init test update body =>
    (init.map varUsesNumber).getD false || (test.map exprUsesNumber).getD false ||
      (update.map exprUsesNumber).getD false || stmtUsesNumber body
  | .whileStmt _ test body => exprUsesNumber test || stmtUsesNumber body
  | .block _ body => stmtsUseNumber body
  | _ => false

def stmtsUseNumber : List Stmt → Bool
  | [] => false
  | s :: rest => stmtUsesNumber s || stmtsUseNumber rest

end

/-- The file uses the number model: a `number` type, a number literal, the
name `Number`, `NaN` or `Infinity`, or a read of `length` or `indexOf`
anywhere. A file can use `Number.isNaN(NaN)` or `a.length === b.length` with
no `number` keyword, and it still needs `N`. -/
def moduleUsesNumber (m : Module) : Bool :=
  m.decls.any fun
    -- An import of one of these names is refused, so an import adds nothing.
    -- An export list names declarations that the other cases see.
    | .import .. | .exports .. => false
    | .function _ _ name _ params ret body =>
      isNumberName name ||
        params.any (fun p => isNumberName p.name || (p.type.map typeUsesNumber).getD false) ||
        (ret.map typeUsesNumber).getD false || stmtUsesNumber body
    | .interface _ _ name _ fields =>
      isNumberName name || fields.any fun f => isNumberName f.name || typeUsesNumber f.type
    | .typeAlias _ _ name _ type => isNumberName name || typeUsesNumber type
    | .enum _ _ name _ => isNumberName name
    | .exportedVar _ d => varUsesNumber d
    | .stmt st => stmtUsesNumber st

/-! ### The module -/

/-- The string enum named `name` that `iface` exports, with the name and the
string of each member. -/
def Interface.stringEnum? (iface : Interface) (name : String) : Option (EnumInfo × List (String × String)) := do
  let info ← iface.enums.find? fun e => e.name == name && e.exported
  let pairs ← info.named
  return (info, pairs)

/-- `import { a, type B } from "./x.ts"`. Each name becomes a function, a
string enum or a type of the file, as the file it names exports it. That file
must be translated first. -/

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
      match iface.stringEnum? n.name with
      -- A string enum is a value too: its object, whose members code reads.
      | some (info, pairs) =>
        modify fun c => { c with
          enums := c.enums ++ [{ info with exported := false }],
          enumValues := c.enumValues ++ [{ name := n.name, ref := info.ref, members := pairs }] }
      | none =>
      if iface.aliases.any (·.name == n.name) || (iface.enums.any fun e => e.name == n.name && e.exported) ||
          iface.unions.any fun u => u.name == n.name && u.exported then
        reject n.span s!"'{n.name}' is a type; import it with 'type {n.name}'"
      let fn ← orReject (iface.functions.find? (·.name == n.name)) n.span
        s!"'{source}' exports no function named '{n.name}'"
      modify fun c => { c with functions := c.functions ++ [{ fn with exported := false }] }

/-- Why the export list `names` is wrong in `c`, if it is. Each name must be
a function, or with `type` an interface or a type, that the file declares
before the list and does not export already. Node's type stripping removes a
name with `type`, so a function may not have it, and a type must. A string
enum is also a value, so only `export enum` exports it. -/
def exportsError? (c : Ctx) (names : List ImportName) : Option (Span × String) :=
  names.findSome? fun n =>
    if c.enums.any fun e => e.file == c.file && e.name == n.name && e.named.isSome then
      some (n.span, s!"'{n.name}' is a string enum; export it with 'export enum {n.name}'")
    else
      let ownFn := c.functions.find? fun f => f.file == c.file && f.name == n.name
      let ownType : Option Bool :=
        ((c.structs.find? fun i => i.file == c.file && i.name == n.name).map (·.exported)).orElse fun _ =>
        ((c.aliases.find? fun a => a.file == c.file && a.name == n.name).map (·.exported)).orElse fun _ =>
        ((c.enums.find? fun e => e.file == c.file && e.name == n.name).map (·.exported)).orElse fun _ =>
        (c.unions.find? fun u => u.file == c.file && u.name == n.name).map (·.exported)
      if n.typeOnly then
        match ownType with
        | some true => some (n.span, s!"'{n.name}' is exported already")
        | some false => none
        | none => some (n.span, s!"this file declares no interface or type named '{n.name}' before this export list")
      else
        match ownFn, ownType with
        | some f, _ => if f.exported then some (n.span, s!"'{n.name}' is exported already") else none
        | none, some _ => some (n.span, s!"'{n.name}' is a type; export it with 'type {n.name}'")
        | none, none =>
          some (n.span, s!"this file declares no function named '{n.name}' before this export list")

/-- One declaration: an output declaration, or none for an import or an
export list. -/
def translateDecl (thr : String → Bool) : Decl → TM (Option IR.Decl)
  | .import s names source => do translateImport s names source; return none
  | .exports s names source => do
    if source.isSome then
      reject s "tolean does not translate a re-export such as 'export { a } from \"./x.ts\"'; import the names instead"
    if let some (sp, msg) := exportsError? (← get) names then reject sp msg
    return none
  | .interface s exported name typeParams fields => some <$> translateInterface s exported name typeParams fields
  | .typeAlias s exported name typeParams type => some <$> translateAlias s exported name typeParams type
  | .function s exported name typeParams params ret body =>
    some <$> translateFunction thr s exported name typeParams params ret body
  | .enum s exported name members => some <$> translateStringEnum s exported name members
  | d => reject d.span "only imports, interfaces, types, enums and functions may appear at top level"

/-- The names of the export lists of `m` that name declarations of the file:
`export { a, type B }`. -/
def exportListed (m : Module) : List ImportName :=
  m.decls.flatMap fun
    | .exports _ names none => names
    | _ => []

/-- A name that two export lists of `m` name, or one list twice. -/
def duplicateExport? (m : Module) : Option ImportName :=
  let listed := exportListed m
  listed.zipIdx.findSome? fun (n, i) =>
    if (listed.take i).any (·.name == n.name) then some n else none

/-- The declarations of `m`, translated. This is the translator as a function
from one syntax tree to another: `translate` parses the source before it and
prints the result after it. -/
def translateDecls (m : Module) : TM (List IR.Decl) := do
  if let some n := duplicateExport? m then reject n.span s!"'{n.name}' is in two export lists"
  return (← m.decls.mapM (translateDecl (Eval.mayThrow m))).filterMap id

mutual

/-- The declarations that a type names: interfaces, literal unions and
tagged unions. -/
def Ty.declRefs : Ty → List DeclRef
  | .struct r args => r :: Ty.declRefsList args
  | .enum r | .tagged r _ => [r]
  | .nullable t | .optional t | .array t => t.declRefs
  | .tuple ts => Ty.declRefsList ts
  | .map k v => k.declRefs ++ v.declRefs
  | .set t => t.declRefs
  | _ => []

def Ty.declRefsList : List Ty → List DeclRef
  | [] => []
  | t :: ts => t.declRefs ++ Ty.declRefsList ts

end

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

/-- `c` with the file's own declarations that `listed` names marked as
exported: functions by the names without `type`, and types by the names with
it. -/
def Ctx.withExports (c : Ctx) (listed : List ImportName) : Ctx :=
  let fns := (listed.filter (!·.typeOnly)).map (·.name)
  let tys := (listed.filter (·.typeOnly)).map (·.name)
  let mark (file name : String) (names : List String) : Bool := file == c.file && names.contains name
  { c with
    functions := c.functions.map fun f => if mark f.file f.name fns then { f with exported := true } else f
    structs := c.structs.map fun i => if mark i.file i.name tys then { i with exported := true } else i
    aliases := c.aliases.map fun a => if mark a.file a.name tys then { a with exported := true } else a
    enums := c.enums.map fun e =>
      if e.named.isNone && mark e.file e.name tys then { e with exported := true } else e
    unions := c.unions.map fun u => if mark u.file u.name tys then { u with exported := true } else u }

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
  | .ok decls ctx' => return (m, names, decls, (ctx'.withExports (exportListed m)).interface usesNumber names.typeParam)

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
  -- A string is a `JSString`, which the output names only in a file that
  -- uses strings, so only such a file imports it.
  let usesString := decls.any (IR.Decl.usesString IR.ExprExt.usesString)
  -- The same for a map, which is a `JSMap`.
  let usesMap := decls.any (IR.Decl.usesMap IR.ExprExt.onMap)
  -- A function that can throw returns `Except JSError R`, and `JSError`
  -- holds a string.
  let throws := decls.any fun
    | .function _ _ (.except ..) _ => true
    | _ => false
  let header :=
    (if names.generic then ["import tolean.TypeScript.Spec.Number"] else []) ++
    (if throws then ["import tolean.TypeScript.Spec.Error"]
     else if usesString then ["import tolean.TypeScript.Spec.String"] else []) ++
    (if usesMap then ["import tolean.TypeScript.Map"] else []) ++
    (if decls.any (IR.Decl.recursive names.file) then ["import tolean.TypeScript.Decreasing"] else []) ++
    imports ++
    (if names.generic || usesString || throws || usesMap then ["", "open tolean.TypeScript"]
     else if imports.isEmpty then [] else [""])
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
