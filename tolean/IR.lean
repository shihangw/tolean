import tolean.Sexp
import tolean.Source

/-!
The Tolean IR, the Tolean intermediate representation: the Lean code that a
translator writes, as Lean data.

This file holds the part of the IR that every language shares, because every
language translates into Lean: integers, booleans, strings, `Option`, `if`,
`let`, structures, lists and `List.foldl`. A language adds its own types and
operations at two extension points. `Ty T` has a case `ext` for a type of `T`,
and `Expr T E` has a case `ext` for an operation of `E` on a list of
arguments. TypeScript, for example, adds JavaScript numbers and `null` in
`tolean/TypeScript/IR.lean`.

The translator builds the IR, and `print` writes it as text. Each constructor
is one form that the output can take. The printer asks the language how to
write its own types and operations, through the classes `PrintTy` and
`PrintOp`. `docs/decisions/2026-10-30-tolean-ir.md` explains why the IR is a
type of its own rather than `Lean.Expr`.

The printer is total, and it reads nothing but the IR and the names of the
file (`Names`).
-/
namespace tolean.IR

/-- Words that Lean reads as keywords, so a plain name cannot be one. -/
def leanReserved : List String :=
  ["_root_", "abbrev", "at", "axiom", "by", "class", "def",
   "deriving", "do", "else", "end", "example", "extends", "for", "from", "fun", "have", "if",
   "import", "in", "inductive", "instance", "let", "match", "mut", "namespace", "open",
   "private", "protected", "return", "section", "show", "structure", "then", "theorem",
   "universe", "unless", "variable", "where", "with", "Type", "Prop", "Sort"]

/-- A Lean type in the output. `T` holds the types that a language adds. -/
inductive Ty (T : Type) where
  | int | bool | string
  | option (value : Ty T)
  /-- `Option T`, for a value that a language leaves out rather than setting to
  a null, such as TypeScript's optional field `f?: T`. A structure gives such
  a field the default `none`, so that an instance can leave it out too. -/
  | optional (value : Ty T)
  | list (elem : Ty T)
  /-- A structure of the program: one that the file declares, or one that it
  imports. -/
  | struct (ref : DeclRef)
  /-- An inductive type of the program whose constructors take no arguments,
  such as the type of the TypeScript literal union `type T = 'a' | 'b'`. -/
  | enum (ref : DeclRef)
  /-- An inductive type with one constructor for each member of a tagged
  union, each of which holds a value of the member: a union of structures,
  such as TypeScript's `type T = A | B`, or a union of primitive types, such
  as `type T = string | bigint`. -/
  | tagged (ref : DeclRef)
  /-- The type of a tag field, such as `kind: 'circle'`. A structure leaves
  the field out, because its value never changes. -/
  | tag (value : String)
  /-- A type that the language adds. -/
  | ext (t : T)
deriving BEq, Repr, Inhabited

/-- `+`, `-` and `*` on `Int`. -/
inductive IntOp where
  | add | sub | mul
deriving BEq, Repr, Inhabited

/-- An order on `Int`, which is a `Prop`. -/
inductive Order where
  | lt | le | gt | ge
deriving BEq, Repr, Inhabited

/-- `Int.tdiv` and `Int.tmod`. -/
inductive Division where
  | tdiv | tmod
deriving BEq, Repr, Inhabited

/-- A Lean expression in the output. Some are a `Prop`, such as `a < b`; the
translator knows which, and wraps one in `decide` where Lean needs a `Bool`.
`T` holds the types that a language adds, and `E` its operations. -/
inductive Expr (T E : Type) where
  /-- `(n : Int)`. The translator gives it only a literal's value, which is
  not negative. -/
  | int (n : Int)
  | none
  | bool (b : Bool)
  | string (s : String)
  | var (name : String)
  /-- `x.f`, or `(e).f` when `wrap` is true. -/
  | field (obj : Expr T E) (wrap : Bool) (name : String)
  /-- `¬(p)`, on a `Prop`. -/
  | propNot (p : Expr T E)
  /-- `!(b)`, on a `Bool`. -/
  | not (b : Expr T E)
  /-- `(-a)`, on an `Int`. -/
  | neg (a : Expr T E)
  /-- `(if c then a else b)`. -/
  | ite (c a b : Expr T E)
  /-- `(f a b)`: a call of a function of the program, one that the file
  declares or one that it imports. When the function is generic over the type
  parameter, the call passes it by name: `(f (N := N) a b)`. -/
  | call (ref : DeclRef) (args : List (Expr T E))
  /-- `([a, b] : List T)`, where `elem` is `T`. -/
  | list (elems : List (Expr T E)) (elem : Ty T)
  /-- `({ f := a, g := b } : S)`. -/
  | struct (fields : List (String × Expr T E)) (ref : DeclRef)
  /-- `a.isNone`. -/
  | isNone (a : Expr T E)
  /-- `a.isSome`. -/
  | isSome (a : Expr T E)
  /-- `(match x with | none => a | some x => b)`. -/
  | matchNull (name : String) (whenNull whenValue : Expr T E)
  /-- `T.a`: the constructor `a` of the inductive type `T`. -/
  | enumCase (ref : DeclRef) (member : String)
  /-- The value of a tag field in a structure instance, such as `kind:
  'circle'`. The printer leaves it out, because the structure has no such
  field, but the source's object has it. -/
  | tagValue (value : String)
  /-- `(T.a e)`: the member `a` of a tagged union `T`, from the value `e` of
  that member. -/
  | inject (ref : DeclRef) (tag : String) (e : Expr T E)
  /-- `(Option.getD a b)`, or `(Option.or a b)` when `nullable` is true: the
  value of `a ?? b`. `b` is a `T` in the first, and an `Option T` in the
  second. -/
  | coalesce (a b : Expr T E) (nullable : Bool)
  /-- `(a + b)`. -/
  | intOp (op : IntOp) (a b : Expr T E)
  /-- `a < b`, a `Prop`. -/
  | order (op : Order) (a b : Expr T E)
  /-- `(Int.tdiv a b)`. -/
  | division (op : Division) (a b : Expr T E)
  /-- `a = b`, a `Prop`. -/
  | eq (a b : Expr T E)
  /-- `a ≠ b`, a `Prop`. -/
  | ne (a b : Expr T E)
  /-- `(p) ∧ (q)`, on two `Prop`s. -/
  | propAnd (p q : Expr T E)
  /-- `(p) ∨ (q)`, on two `Prop`s. -/
  | propOr (p q : Expr T E)
  /-- `(a && b)`, on two `Bool`s. -/
  | and (a b : Expr T E)
  /-- `(a || b)`, on two `Bool`s. -/
  | or (a b : Expr T E)
  /-- `decide (p)`: a `Prop` as a `Bool`. -/
  | decide (p : Expr T E)
  /-- `xs ++ [a]`: the new value of an owned array after a push. -/
  | push (name : String) (a : Expr T E)
  /-- `x + a`: the new value of a `let` local after `x += a`. -/
  | update (op : IntOp) (name : String) (a : Expr T E)
  /-- An operation that the language adds, on `args`. -/
  | ext (op : E) (args : List (Expr T E))
deriving Repr, Inhabited

/-- What a certificate needs to know about a loop, besides its code. The
printer does not read it. -/
structure LoopInfo (T : Type) where
  /-- The span of the `for…of` statement. -/
  span : Span
  /-- The types of the locals that the loop changes, in the order of the state. -/
  stateTypes : List (Ty T)
  /-- The type of the elements. -/
  elem : Ty T
  /-- The other locals in scope at the loop, in the order they were declared. -/
  scope : List (String × Ty T)
deriving Repr, Inhabited

/-- The body of a function: `let`s that end in a value. -/
inductive Body (T E : Type) where
  /-- The value of the function. -/
  | value (e : Expr T E)
  /-- The locals that a branch or a loop body changes: `x` or `(x, y)`. -/
  | state (names : List String)
  /-- `let x := e`, then `rest`. -/
  | «let» (name : String) (e : Expr T E) (rest : Body T E)
  /-- `let xs : T := [a, b]`: an owned array, then `rest`. -/
  | letArray (name : String) (type : Ty T) (elems : List (Expr T E)) (rest : Body T E)
  /-- `if c then … else …`. -/
  | ite (c : Expr T E) (whenTrue whenFalse : Body T E)
  /-- `match x with | none => … | some x => …`. -/
  | matchNull (name : String) (whenNull whenValue : Body T E)
  /-- `match x with | T.a x => … | T.b x => …`: a test of the tag of `x`, a
  value of the tagged union `T`. The tag is the tag field `field` of the
  source's value, or its type, such as TypeScript's `typeof x`, when `field`
  is none. The first branch is for the tag `tag`. The second names the member
  `other` when it is the only one left, and then runs only for its tag, as
  Lean's `match` does, or else matches every other member. -/
  | matchTag (name : String) (ref : DeclRef) (field : Option String) (tag : String)
      (other : Option String) (whenTag whenOther : Body T E)
  /-- `let (x, y) := branch`, where `branch` is an `ite` or a `matchNull`
  that ends in the state, then `rest`. -/
  | letState (names : List String) (branch : Body T E) (rest : Body T E)
  /-- `let (x, y) := List.foldl (fun (x, y) e => body) (x, y) items`, then
  `rest`. -/
  | fold (names : List String) (element : String) (body : Body T E) (items : Expr T E)
      (rest : Body T E) (info : LoopInfo T)
deriving Repr, Inhabited

/-- A declaration in the output. -/
inductive Decl (T E : Type) where
  /-- `structure S where`, with one field per line. -/
  | struct (name : String) (fields : List (String × Ty T))
  /-- `abbrev T := U`: a type alias. The translator writes the type `U` itself
  wherever the source names `T`, so the output names `T` only here, for the
  claims about it to use. -/
  | alias (name : String) (type : Ty T)
  /-- `inductive T where | a | b`, with decidable equality: a type whose
  constructors take no arguments. -/
  | enum (name : String) (members : List String)
  /-- `inductive T where | a (value : A) | b (value : B)`: a tagged union,
  with the tag and the type of each member. The source's values tell the
  members apart by the field `field`, as objects of a union of structures do,
  or by their type when `field` is none, as values of a union of primitive
  types do. -/
  | tagged (name : String) (field : Option String) (members : List (String × Ty T))
  /-- `def f (x : T) : R :=`, then the body. -/
  | function (name : String) (params : List (String × Ty T)) (ret : Ty T) (body : Body T E)
deriving Repr, Inhabited

variable {T E : Type}

/-! ### The declarations that the output names -/

def Ty.refs : Ty T → List DeclRef
  | .struct r | .enum r | .tagged r => [r]
  | .option t | .optional t | .list t => t.refs
  | _ => []

mutual

/-- The functions and structures of the program that `e` names. -/
def Expr.refs : Expr T E → List DeclRef
  | .call r args => r :: Expr.refsList args
  | .list elems t => Expr.refsList elems ++ t.refs
  | .struct fields r => r :: Expr.refsFields fields
  | .ext _ args => Expr.refsList args
  | .field a _ _ | .propNot a | .not a | .neg a | .isNone a | .isSome a
  | .decide a | .push _ a | .update _ _ a => a.refs
  | .ite a b c => a.refs ++ b.refs ++ c.refs
  | .matchNull _ a b | .coalesce a b _ | .intOp _ a b | .order _ a b | .division _ a b
  | .eq a b | .ne a b | .propAnd a b | .propOr a b | .and a b | .or a b =>
    a.refs ++ b.refs
  | .enumCase r _ => [r]
  | .inject r _ e => r :: e.refs
  | .tagValue _ => []
  | .int _ | .none | .bool _ | .string _ | .var _ => []

def Expr.refsList : List (Expr T E) → List DeclRef
  | [] => []
  | e :: es => e.refs ++ Expr.refsList es

def Expr.refsFields : List (String × Expr T E) → List DeclRef
  | [] => []
  | (_, e) :: fs => e.refs ++ Expr.refsFields fs

end

def Body.refs : Body T E → List DeclRef
  | .value e => e.refs
  | .state _ => []
  | .let _ e rest => e.refs ++ rest.refs
  | .letArray _ t elems rest => t.refs ++ Expr.refsList elems ++ rest.refs
  | .ite c a b => c.refs ++ a.refs ++ b.refs
  | .matchNull _ a b | .letState _ a b => a.refs ++ b.refs
  | .matchTag _ r _ _ _ a b => r :: (a.refs ++ b.refs)
  | .fold _ _ body items rest _ => body.refs ++ items.refs ++ rest.refs

/-- The functions and structures of the program that `d` names. -/
def Decl.refs : Decl T E → List DeclRef
  | .struct _ fields => fields.flatMap (·.2.refs)
  | .alias _ type => type.refs
  | .enum .. => []
  | .tagged _ _ members => members.flatMap (·.2.refs)
  | .function _ params ret body => params.flatMap (·.2.refs) ++ ret.refs ++ body.refs

/-! ### Printing -/

/-- Another file of the program, as the output of a file that imports from it
writes its declarations. -/
structure ImportedFile where
  /-- The namespace of its translation. -/
  ns : String
  /-- Its declarations are generic over the type parameter. -/
  generic : Bool
  /-- The name under which its declarations bind the type parameter. -/
  typeParam : String

/-- The names that the printer needs from the file. -/
structure Names where
  /-- Lean names the output uses that the source also declares. The output
  writes them in full from the root, so a source name never hides them. -/
  clashes : List String := []
  /-- The type parameter that a language may make every declaration generic
  over, such as the number type of TypeScript: `N`, or a fresh name when the
  source uses `N`. -/
  typeParam : String := "N"
  /-- Every declaration of the file is generic over the type parameter. -/
  generic : Bool := false
  /-- The namespace of the translation, with a final dot, before the names of
  its structures and functions. The translation itself writes them inside
  that namespace, so it leaves this empty; a certificate, outside it, sets it. -/
  namespacePrefix : String := ""
  /-- The file of the translation. The output writes a declaration of another
  file with the namespace of that file's translation. -/
  file : String := ""
  /-- The files that the file imports from, by path. -/
  imported : List (String × ImportedFile) := []

/-- How the output writes the declaration `r`, and the name under which it
binds the type parameter when it is generic over it. -/
def Names.ref (names : Names) (r : DeclRef) : String × Option String :=
  if r.file == names.file then
    (names.namespacePrefix ++ r.name, if names.generic then some names.typeParam else none)
  else match names.imported.lookup r.file with
    -- From the root, so that a local name or the current namespace cannot
    -- capture it.
    | some i => ("_root_." ++ i.ns ++ "." ++ r.name, if i.generic then some i.typeParam else none)
    | none => (r.name, none)

/-- The Lean names that the shared part of the output uses, with their full
names from the root. -/
def leanNames : List (String × String) :=
  [("decide", "Decidable.decide"), ("List", "List"), ("Option", "Option"),
   ("some", "Option.some"), ("none", "Option.none"), ("Int", "Int"), ("Bool", "Bool"),
   ("String", "String"), ("DecidableEq", "DecidableEq"), ("Repr", "Repr")]

/-- Write the Lean name `name` (or `name.rest`), from the root when the source
declares the same name. `table` gives the full names. -/
def leanNameIn (table : List (String × String)) (names : Names) (name : String) : String :=
  let (head, rest) := match name.splitOn "." with
    | h :: t => (h, String.join (t.map ("." ++ ·)))
    | [] => (name, "")
  if names.clashes.contains head then s!"_root_.{(table.lookup head).getD head}{rest}"
  else name

/-- Write a Lean name of the shared part of the output. -/
def leanName (names : Names) (name : String) : String := leanNameIn leanNames names name

/-- Lean code as an argument: parenthesized unless it is one atom. A prefix
`!` or `¬` takes the rest of the line in Lean, so code that starts with one is
not an atom even without a space: `f !(a) b` reads as `f !((a) b)`. -/
def argument (code : String) : String :=
  if code.contains ' ' || code.startsWith "!" || code.startsWith "¬" then s!"({code})" else code

def wrapped (constructor argument : String) : String :=
  constructor ++ " " ++
    (if argument.contains ' ' && !argument.startsWith "(" then s!"({argument})" else argument)

def tuple (names : List String) : String :=
  match names with
  | [name] => name
  | _ => "(" ++ ", ".intercalate names ++ ")"

def indentBy (by_ : String) (lines : List String) : List String := lines.map (by_ ++ ·)

def indent (lines : List String) : List String := indentBy "  " lines

/-- A constructor of an inductive type as the output names it: always in
`«»`. Lean reads some words as keywords or modifiers, such as `open` or
`unsafe`, and no list of them stays complete across Lean versions. The
quotes change only how the name is written, so a claim can still name the
constructor `T.closed`. -/
def memberName (member : String) : String := s!"«{member}»"

/-- How a language prints the types it adds. -/
class PrintTy (T : Type) where
  /-- The type `t`. -/
  print : Names → T → String
  /-- The printed type names the type parameter. -/
  namesParam : Names → T → Bool
  /-- What a function that is generic over the type parameter binds after its
  name, such as ` {N : Type} [JSNumber N]`. -/
  binders : Names → String

/-- How a language prints the operations it adds, given its arguments as
printed code. -/
class PrintOp (E : Type) where
  print : Names → E → List String → String

def Ty.print [PrintTy T] (names : Names) : Ty T → String
  | .int => leanName names "Int"
  | .bool => leanName names "Bool"
  | .string => leanName names "String"
  | .option t | .optional t => wrapped (leanName names "Option") (t.print names)
  | .list t => wrapped (leanName names "List") (t.print names)
  | .struct ref =>
    match names.ref ref with
    | (name, some _) => s!"({name} {names.typeParam})"
    | (name, Option.none) => name
  | .enum ref => (names.ref ref).1
  | .tagged ref =>
    match names.ref ref with
    | (name, some _) => s!"({name} {names.typeParam})"
    | (name, Option.none) => name
  | .tag _ => leanName names "String"
  | .ext t => PrintTy.print names t

/-- The printed type names the type parameter, so a declaration of it must
bind it. -/
def Ty.namesParam [PrintTy T] (names : Names) : Ty T → Bool
  | .struct ref | .tagged ref => (names.ref ref).2.isSome
  | .option t | .optional t | .list t => t.namesParam names
  | .ext t => PrintTy.namesParam names t
  | _ => false

def IntOp.symbol : IntOp → String
  | .add => "+" | .sub => "-" | .mul => "*"

def Order.symbol : Order → String
  | .lt => "<" | .le => "≤" | .gt => ">" | .ge => "≥"

def Division.name : Division → String
  | .tdiv => "tdiv" | .tmod => "tmod"

/-! The values that the shared operations on `Int` compute. -/

def IntOp.apply : IntOp → Int → Int → Int
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·)

def Order.apply : Order → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)

def Division.apply : Division → Int → Int → Int
  | .tdiv => Int.tdiv | .tmod => Int.tmod

/-- The body tests the tag of the local `name` somewhere. -/
def Body.testsTag (name : String) : Body T E → Bool
  | .matchTag n _ _ _ _ a b => n == name || a.testsTag name || b.testsTag name
  | .let _ _ rest | .letArray _ _ _ rest => rest.testsTag name
  | .ite _ a b | .matchNull _ a b | .letState _ a b => a.testsTag name || b.testsTag name
  | .fold _ _ body _ rest _ => body.testsTag name || rest.testsTag name
  | .value _ | .state _ => false

section
variable [PrintTy T] [PrintOp E]

/-- The type of a loop's state, such as `Int × Bool`. -/
def foldState (names : Names) (info : LoopInfo T) : String :=
  " × ".intercalate (info.stateTypes.map (·.print names))

/-- The binders of the function that `List.foldl` runs for a loop, with their
types: `((x, y) : Int × Bool) (e : T)`. Lean elaborates the body before it
knows the types, so in `{ f := e }` with a field of type `Option N` it would
take `e` to be an `Option N`, not an `N` to wrap. -/
def foldBinders (names : Names) (state : List String) (element : String) (info : LoopInfo T) :
    String :=
  s!"({tuple state} : {foldState names info}) ({element} : {info.elem.print names})"

mutual

def Expr.print (names : Names) : Expr T E → String
  | .int n => s!"({n} : {leanName names "Int"})"
  | .none => leanName names "none"
  | .bool b => if b then "true" else "false"
  | .string s => Sexp.quote s
  | .var name => name
  | .enumCase ref member => s!"{(names.ref ref).1}.{memberName member}"
  | .tagValue value => Sexp.quote value
  | .inject ref tag e => s!"({(names.ref ref).1}.{memberName tag} {argument (e.print names)})"
  | .field obj wrap name =>
    let o := obj.print names
    s!"{if wrap then s!"({o})" else o}.{name}"
  | .propNot p => s!"¬({p.print names})"
  | .not b => s!"!({b.print names})"
  | .neg a => s!"(-{a.print names})"
  | .ite c a b => s!"(if {c.print names} then {a.print names} else {b.print names})"
  | .call ref args =>
    -- The function binds the type parameter under its own name, `N` or a
    -- fresh one.
    let head := match names.ref ref with
      | (name, some binder) => [name, s!"({binder} := {names.typeParam})"]
      | (name, Option.none) => [name]
    "(" ++ " ".intercalate (head ++ (Expr.printList names args).map argument) ++ ")"
  | .list elems elem =>
    s!"([{", ".intercalate (Expr.printList names elems)}] : {(Ty.list elem).print names})"
  | .struct fields ref =>
    "({ " ++ ", ".intercalate (Expr.printFields names fields) ++ " } : " ++
      (Ty.struct ref : Ty T).print names ++ ")"
  | .isNone a => s!"{argument (a.print names)}.isNone"
  | .isSome a => s!"{argument (a.print names)}.isSome"
  | .matchNull name whenNull whenValue =>
    s!"(match {name} with | {leanName names "none"} => {whenNull.print names} | " ++
      s!"{leanName names "some"} {name} => {whenValue.print names})"
  | .coalesce a b nullable =>
    let fn := leanName names (if nullable then "Option.or" else "Option.getD")
    s!"({fn} {argument (a.print names)} {argument (b.print names)})"
  | .intOp op a b => s!"({a.print names} {op.symbol} {b.print names})"
  | .order op a b => s!"{a.print names} {op.symbol} {b.print names}"
  | .division op a b =>
    s!"({leanName names "Int"}.{op.name} {argument (a.print names)} {argument (b.print names)})"
  | .eq a b => s!"{a.print names} = {b.print names}"
  | .ne a b => s!"{a.print names} ≠ {b.print names}"
  | .propAnd p q => s!"({p.print names}) ∧ ({q.print names})"
  | .propOr p q => s!"({p.print names}) ∨ ({q.print names})"
  | .and a b => s!"({a.print names} && {b.print names})"
  | .or a b => s!"({a.print names} || {b.print names})"
  | .decide p => s!"{leanName names "decide"} ({p.print names})"
  | .push name a => s!"{name} ++ [{a.print names}]"
  | .update op name a => s!"{name} {op.symbol} {a.print names}"
  | .ext op args => PrintOp.print names op (Expr.printList names args)

def Expr.printList (names : Names) : List (Expr T E) → List String
  | [] => []
  | e :: es => e.print names :: Expr.printList names es

def Expr.printFields (names : Names) : List (String × Expr T E) → List String
  | [] => []
  | (key, e) :: fs =>
    match e with
    -- The structure has no tag field.
    | .tagValue _ => Expr.printFields names fs
    | _ => s!"{key} := {e.print names}" :: Expr.printFields names fs

end

mutual

/-- The lines of a body. -/
def Body.lines (names : Names) : Body T E → List String
  | .value e => [e.print names]
  | .state ns => [tuple ns]
  | .let name e rest => s!"let {name} := {e.print names}" :: rest.lines names
  | .letArray name type elems rest =>
    s!"let {name} : {type.print names} := [{", ".intercalate (Expr.printList names elems)}]" ::
      rest.lines names
  | .ite c whenTrue whenFalse =>
    [s!"if {c.print names} then"] ++ indent (whenTrue.lines names) ++ ["else"] ++
      indent (whenFalse.lines names)
  | .matchNull name whenNull whenValue =>
    [s!"match {name} with", s!"| {leanName names "none"} =>"] ++ indent (whenNull.lines names) ++
      [s!"| {leanName names "some"} {name} =>"] ++ indent (whenValue.lines names)
  | .matchTag name ref _ tag other whenTag whenOther =>
    let ctor (t : String) := s!"{(names.ref ref).1}.{memberName t}"
    let rest : List String := match other with
      | some t => s!"| {ctor t} {name} =>" :: indent (whenOther.lines names)
      | Option.none =>
        match whenOther with
        | .matchTag n .. =>
          if n == name then Body.tagArms names name whenOther
          else s!"| {name} =>" :: indent (whenOther.lines names)
        | _ => s!"| {name} =>" :: indent (whenOther.lines names)
    s!"match {name} with" :: s!"| {ctor tag} {name} =>" :: indent (whenTag.lines names) ++ rest
  | .letState ns branch rest =>
    [s!"let {tuple ns} :="] ++ indent (branch.lines names) ++ rest.lines names
  | .fold ns element body items rest info =>
    let bodyLines := body.lines names
    let lastLine := bodyLines.getLast?.getD ""
    [s!"let {tuple ns} :=", s!"  {leanName names "List.foldl"}",
      s!"    (fun {foldBinders names ns element info} =>"] ++
      indentBy "      " (bodyLines.dropLast ++ [lastLine ++ ")"]) ++
      [s!"    {tuple ns} {items.print names}"] ++ rest.lines names

/-- The arms of `match name with` for a test of its tag, nested in the arm
for the other members of a test of the same local. They join the outer
`match`, so that Lean sees that the arms cover every member: a nested
`match` would not know which members the outer one ruled out. -/
def Body.tagArms (names : Names) (name : String) : Body T E → List String
  | .matchTag _ ref _ tag other whenTag whenOther =>
    let ctor (t : String) := s!"{(names.ref ref).1}.{memberName t}"
    let rest : List String := match other with
      | some t => s!"| {ctor t} {name} =>" :: indent (whenOther.lines names)
      | Option.none =>
        match whenOther with
        | .matchTag n .. =>
          if n == name then Body.tagArms names name whenOther
          else s!"| {name} =>" :: indent (whenOther.lines names)
        | _ => s!"| {name} =>" :: indent (whenOther.lines names)
    s!"| {ctor tag} {name} =>" :: indent (whenTag.lines names) ++ rest
  -- `Body.lines` calls this only on a test of a tag.
  | _ => []

end

def Decl.print (names : Names) : Decl T E → String
  | .struct name fields =>
    let generic := if names.generic then s!" ({names.typeParam} : Type)" else ""
    -- A tag field never changes, so the structure leaves it out.
    let kept := fields.filter fun (_, type) => !(type matches .tag _)
    "\n".intercalate (s!"structure {name}{generic} where" ::
      kept.map fun (field, type) =>
        let default := if type matches .optional _ then s!" := {leanName names "none"}" else ""
        s!"  {field} : {type.print names}{default}")
  | .tagged name _ members =>
    let generic := if names.generic then s!" ({names.typeParam} : Type)" else ""
    "\n".intercalate (s!"inductive {name}{generic} where" ::
      members.map fun (tag, type) => s!"  | {memberName tag} (value : {type.print names})")
  | .enum name members =>
    "\n".intercalate (s!"inductive {name} where" ::
      members.map (s!"  | {memberName ·}") ++
      [s!"deriving {leanName names "DecidableEq"}, {leanName names "Repr"}"])
  | .alias name type =>
    let generic := if type.namesParam names then s!" ({names.typeParam} : Type)" else ""
    s!"abbrev {name}{generic} := {type.print names}"
  | .function name params ret body =>
    let generic := if names.generic then PrintTy.binders (T := T) names else ""
    let leanParams := params.map fun (param, type) => s!"({param} : {type.print names})"
    "\n".intercalate
      (s!"def {name}{generic} {" ".intercalate leanParams} : {ret.print names} :=" ::
        indent (body.lines names))

end

end tolean.IR
