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
   "universe", "unless", "variable", "where", "with", "Type", "Prop", "Sort",
   -- Lean's parser reads these as keywords too, so a parameter or local with
   -- such a name would not parse.
   "attribute", "binder_predicate", "builtin_initialize", "calc", "coinductive",
   "declare_syntax_cat", "decreasing_by", "elab", "elab_rules", "hiding", "include", "infix",
   "infixl", "infixr", "initialize", "local", "macro", "macro_rules", "meta", "mutual",
   "nofun", "nomatch", "noncomputable", "nonrec", "notation", "omit", "opaque", "partial",
   "postfix", "prefix", "public", "renaming", "scoped", "set_option", "show_term", "sorry",
   "suffices", "syntax", "termination_by", "unif_hint", "unsafe", "using"]

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
  /-- `A × B × C`: a tuple of two elements or more, such as TypeScript's
  `[A, B, C]`. Lean nests the product to the right, so `[A, [B, C]]` has the
  same Lean type, and the list of elements keeps the two apart. -/
  | tuple (elems : List (Ty T))
  /-- A type parameter of a generic function, such as `T` in TypeScript's
  `function first<T>(xs: T[]): T | null`. -/
  | param (name : String)
  /-- A generic structure of the program applied to types, such as `Box Int`
  for TypeScript's `Box<bigint>`. -/
  | app (ref : DeclRef) (args : List (Ty T))
  /-- A map from `key` to `value` that keeps its entries in the order that
  each key was first added, such as TypeScript's `Map<K, V>`. The language
  names the Lean type of such a map. -/
  | map (key value : Ty T)
  /-- A set of `elem` that keeps its elements in the order that each was
  first added, such as TypeScript's `Set<T>`. The language names its Lean
  type. -/
  | set (elem : Ty T)
  /-- `Except E V`: the result of a function that can throw an `E`, and that
  returns a `V` when it does not. -/
  | except (error value : Ty T)
  /-- A type that the language adds. -/
  | ext (t : T)
deriving Repr, Inhabited

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

/-- A function on lists that takes a function on the elements: `List.map`,
`List.filter`, `List.any`, `List.all` and `List.find?`, or `List.mapIdx`,
whose function also takes the position of the element, bound to `index`.
`findIndex` is the position of the first element that passes, as the
language writes an index, and `findLast` is `List.find?` on the reversed
list. `sortWith` sorts the list by a comparator, whose function takes two
elements: the first under the parameter's name, the second under `other`. -/
inductive ListMethod where
  | map | filter | any | all | find
  | mapIdx (index : String)
  | findIndex | findLast
  | sortWith (other : String)
deriving BEq, Repr, Inhabited

/-- What a certificate needs to know about a callback, besides its code. The
printer does not read it. -/
structure CallbackInfo (T : Type) where
  /-- The span of the call, such as `xs.map(x => e)`. -/
  span : Span
  /-- The type of the callback's value. -/
  result : Ty T
  /-- The locals in scope at the call, in the order they were declared. -/
  scope : List (String × Ty T)
deriving Repr, Inhabited

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
  /-- `({ f := a, g := b } : S)`, or `({ … } : (S A))` for a generic structure,
  where `args` are its type arguments. -/
  | struct (fields : List (String × Expr T E)) (ref : DeclRef) (args : List (Ty T))
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
  that member. When `T` is generic over the type parameter, the constructor
  gets it by name: `(T.a (N := N) e)`. -/
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
  /-- `(e : T)`: `e` with its type written out, where Lean cannot infer it,
  such as a `let` of `none` that nothing else uses. -/
  | ascribe (e : Expr T E) (type : Ty T)
  /-- `(a, b, c)`: a tuple of two elements or more. -/
  | tuple (elems : List (Expr T E))
  /-- `e.2.1`: the element `index` of the tuple `e`, which has `size`
  elements. -/
  | proj (e : Expr T E) (index size : Nat)
  /-- `(List.map (fun (x : T) => body) items)`, or another `method` with the
  function `fun (x : T) => body` on the elements of `items`, where `param` is
  `x` and `elem` is `T`. For `List.mapIdx`, the function also binds the
  position of the element, written as the language writes an index. -/
  | listMethod (method : ListMethod) (items : Expr T E) (param : String) (elem : Ty T)
      (body : Expr T E) (info : CallbackInfo T)
  /-- `{ base with f := e, … }`: the structure `base` with the fields `fields`
  set. -/
  | structUpdate (base : Expr T E) (fields : List (String × Expr T E))
  /-- `(List.foldl (fun (acc : A) (x : T) => body) init items)`, where `A` is
  `info.result`, the type of `init` and of `body`, and `elem` is `T`. -/
  | listFold (items init : Expr T E) (acc param : String) (elem : Ty T) (body : Expr T E)
      (info : CallbackInfo T)
deriving Repr, Inhabited

/-- What the printer and a certificate need to know about a loop, besides its
code. -/
structure LoopInfo (T : Type) where
  /-- The span of the `for…of` statement. -/
  span : Span
  /-- The types of the locals that the loop changes, in the order of the state. -/
  stateTypes : List (Ty T)
  /-- The type of the elements. -/
  elem : Ty T
  /-- The other locals in scope at the loop, in the order they were declared. -/
  scope : List (String × Ty T)
  /-- A `break` or a `return` can end the loop. The output then runs it with
  `forIn`, and each run of the body gives a `ForInStep`. -/
  breaks : Bool := false
  /-- The type of the function's value, when a `return` in the body can end
  the function. The loop's state then starts with an `Option` of it, which
  holds the value to return. -/
  returns : Option (Ty T) := none
deriving Repr, Inhabited

/-- The body of a function: `let`s that end in a value. -/
inductive Body (T E : Type) where
  /-- The value of the function. -/
  | value (e : Expr T E)
  /-- The locals that a branch or a loop body changes: `x` or `(x, y)`. -/
  | state (names : List String)
  /-- `ForInStep.yield (x, y)`: the end of one run of the body of a loop that
  a `break` can end, with the locals that the body changes. In a loop that a
  `return` can end (`slot`), the state starts with `none`, for no value to
  return: `ForInStep.yield (none, x, y)`. -/
  | yield (names : List String) (slot : Bool)
  /-- `ForInStep.done (x, y)`: a `break`, which ends its loop with the locals
  that the body changes, after `none` when `slot`. -/
  | done (names : List String) (slot : Bool)
  /-- `ForInStep.done (some e, x, y)`: a `return e` in a loop body, which ends
  the loop, and then the function with the value of `e`. -/
  | exit (e : Expr T E) (names : List String)
  /-- `let x := e`, then `rest`. -/
  | «let» (name : String) (e : Expr T E) (rest : Body T E)
  /-- `let xs : T := [a, b]`: an owned array, then `rest`. -/
  | letArray (name : String) (type : Ty T) (elems : List (Expr T E)) (rest : Body T E)
  /-- `if c then … else …`. -/
  | ite (c : Expr T E) (whenTrue whenFalse : Body T E)
  /-- `match x with | none => … | some x => …`. When `optional` is true, `x`
  is an optional value, whose `none` the source writes as a value left out
  rather than a null, as `Ty.optional` is. -/
  | matchNull (name : String) (optional : Bool) (whenNull whenValue : Body T E)
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
  /-- `let (x, y) := e`, then `rest`: one name for each element of the tuple
  `e`, which has two elements or more. -/
  | letTuple (names : List String) (e : Expr T E) (rest : Body T E)
  /-- `let (x, y) := List.foldl (fun (x, y) e => body) (x, y) items`, then
  `rest`. When a `break` can end the loop (`info.breaks`), it is
  `let (x, y) := Id.run (forIn items (x, y) (fun e (x, y) => body))`. When a
  `return` can end it (`info.returns`), it is
  `match Id.run (forIn items (none, x, y) (fun e (_, x, y) => body)) with`,
  with the arms `| (some r, _) => r` and `| (none, x, y) => rest`. -/
  | fold (names : List String) (element : String) (body : Body T E) (items : Expr T E)
      (rest : Body T E) (info : LoopInfo T)
  /-- `throw e`: the function ends with the error `e`. Its type is an
  `Except`. -/
  | throw (e : Expr T E)
  /-- `(f a b) >>= fun x =>`, then `rest`: a call of a function of the program
  that can throw. The function ends with the error when the call throws, and
  `rest` runs with `x` bound to its value otherwise. -/
  | bind (name : String) (ref : DeclRef) (args : List (Expr T E)) (rest : Body T E)
deriving Repr, Inhabited

/-- A declaration in the output. -/
inductive Decl (T E : Type) where
  /-- `structure S (A : Type) where`, with one field per line. `typeParams`
  are the type parameters of a generic structure, in order. -/
  | struct (name : String) (typeParams : List String) (fields : List (String × Ty T))
  /-- `abbrev T := U`: a type alias. The translator writes the type `U` itself
  wherever the source names `T`, so the output names `T` only here, for the
  claims about it to use. -/
  | alias (name : String) (typeParams : List String) (type : Ty T)
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

mutual

def Ty.refs : Ty T → List DeclRef
  | .struct r | .enum r | .tagged r => [r]
  | .option t | .optional t | .list t => t.refs
  | .tuple ts => Ty.refsList ts
  | .app r args => r :: Ty.refsList args
  | .map k v => k.refs ++ v.refs
  | .set t => t.refs
  | .except e v => e.refs ++ v.refs
  | _ => []

def Ty.refsList : List (Ty T) → List DeclRef
  | [] => []
  | t :: ts => t.refs ++ Ty.refsList ts

end

mutual

/-- The functions and structures of the program that `e` names. -/
def Expr.refs : Expr T E → List DeclRef
  | .call r args => r :: Expr.refsList args
  | .list elems t => Expr.refsList elems ++ t.refs
  | .struct fields r args => r :: (Expr.refsFields fields ++ Ty.refsList args)
  | .ext _ args => Expr.refsList args
  | .field a _ _ | .propNot a | .not a | .neg a | .isNone a | .isSome a
  | .decide a | .push _ a | .update _ _ a => a.refs
  | .ite a b c => a.refs ++ b.refs ++ c.refs
  | .matchNull _ a b | .coalesce a b _ | .intOp _ a b | .order _ a b | .division _ a b
  | .eq a b | .ne a b | .propAnd a b | .propOr a b | .and a b | .or a b =>
    a.refs ++ b.refs
  | .enumCase r _ => [r]
  | .inject r _ e => r :: e.refs
  | .ascribe e t => e.refs ++ t.refs
  | .tuple es => Expr.refsList es
  | .proj e _ _ => e.refs
  | .listMethod _ items _ t body _ => items.refs ++ t.refs ++ body.refs
  | .structUpdate base fields => base.refs ++ Expr.refsFields fields
  | .listFold items init _ _ t body info => items.refs ++ init.refs ++ t.refs ++ body.refs ++ info.result.refs
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
  | .state _ | .yield .. | .done .. => []
  | .exit e _ => e.refs
  | .let _ e rest | .letTuple _ e rest => e.refs ++ rest.refs
  | .letArray _ t elems rest => t.refs ++ Expr.refsList elems ++ rest.refs
  | .ite c a b => c.refs ++ a.refs ++ b.refs
  | .matchNull _ _ a b | .letState _ a b => a.refs ++ b.refs
  | .matchTag _ r _ _ _ a b => r :: (a.refs ++ b.refs)
  | .fold _ _ body items rest _ => body.refs ++ items.refs ++ rest.refs
  | .throw e => e.refs
  | .bind _ r args rest => r :: (Expr.refsList args ++ rest.refs)

/-- The functions and structures of the program that `d` names. -/
def Decl.refs : Decl T E → List DeclRef
  | .struct _ _ fields => fields.flatMap (·.2.refs)
  | .alias _ _ type => type.refs
  | .enum .. => []
  | .tagged _ _ members => members.flatMap (·.2.refs)
  | .function _ params ret body => params.flatMap (·.2.refs) ++ ret.refs ++ body.refs

/-! ### The declarations that name the string type -/

mutual

/-- The printed type names the string type. A tag field has a string type,
but the printer leaves tag fields out. -/
def Ty.usesString : Ty T → Bool
  | .string => true
  | .option t | .optional t | .list t => t.usesString
  | .tuple ts | .app _ ts => Ty.usesStringList ts
  | .map k v => k.usesString || v.usesString
  | .set t => t.usesString
  | .except e v => e.usesString || v.usesString
  | _ => false

def Ty.usesStringList : List (Ty T) → Bool
  | [] => false
  | t :: ts => t.usesString || Ty.usesStringList ts

end

mutual

/-- `e` names the string type or holds a string literal. `opUses` tells
whether an operation that the language adds names the string type, as an
operation on strings does. -/
def Expr.usesString (opUses : E → Bool) : Expr T E → Bool
  | .string _ => true
  | .call _ args => Expr.usesStringList opUses args
  | .ext op args => opUses op || Expr.usesStringList opUses args
  | .list elems t => Expr.usesStringList opUses elems || t.usesString
  | .struct fields _ args => Expr.usesStringFields opUses fields || Ty.usesStringList args
  | .field a _ _ | .propNot a | .not a | .neg a | .isNone a | .isSome a
  | .decide a | .push _ a | .update _ _ a | .inject _ _ a => Expr.usesString opUses a
  | .ite a b c => Expr.usesString opUses a || Expr.usesString opUses b || Expr.usesString opUses c
  | .matchNull _ a b | .coalesce a b _ | .intOp _ a b | .order _ a b | .division _ a b
  | .eq a b | .ne a b | .propAnd a b | .propOr a b | .and a b | .or a b =>
    Expr.usesString opUses a || Expr.usesString opUses b
  | .ascribe e t => Expr.usesString opUses e || t.usesString
  | .tuple es => Expr.usesStringList opUses es
  | .proj e _ _ => Expr.usesString opUses e
  | .listMethod _ items _ t body _ =>
    Expr.usesString opUses items || t.usesString || Expr.usesString opUses body
  | .structUpdate base fields =>
    Expr.usesString opUses base || Expr.usesStringFields opUses fields
  | .listFold items init _ _ t body info =>
    Expr.usesString opUses items || Expr.usesString opUses init || t.usesString ||
      Expr.usesString opUses body || info.result.usesString
  -- The printer leaves a tag value out, as it leaves the tag field out.
  | .int _ | .none | .bool _ | .var _ | .enumCase .. | .tagValue _ => false

def Expr.usesStringList (opUses : E → Bool) : List (Expr T E) → Bool
  | [] => false
  | e :: es => Expr.usesString opUses e || Expr.usesStringList opUses es

def Expr.usesStringFields (opUses : E → Bool) : List (String × Expr T E) → Bool
  | [] => false
  | (_, e) :: fs => Expr.usesString opUses e || Expr.usesStringFields opUses fs

end

def Body.usesString (opUses : E → Bool) : Body T E → Bool
  | .value e => Expr.usesString opUses e
  | .state _ | .yield .. | .done .. => false
  | .exit e _ => Expr.usesString opUses e
  | .let _ e rest | .letTuple _ e rest => Expr.usesString opUses e || Body.usesString opUses rest
  | .letArray _ t elems rest =>
    t.usesString || Expr.usesStringList opUses elems || Body.usesString opUses rest
  | .ite c a b => Expr.usesString opUses c || Body.usesString opUses a || Body.usesString opUses b
  | .matchNull _ _ a b | .letState _ a b | .matchTag _ _ _ _ _ a b =>
    Body.usesString opUses a || Body.usesString opUses b
  | .fold _ _ body items rest info =>
    Body.usesString opUses body || Expr.usesString opUses items || Body.usesString opUses rest ||
      info.stateTypes.any (·.usesString) || info.elem.usesString
  | .throw e => Expr.usesString opUses e
  | .bind _ _ args rest => Expr.usesStringList opUses args || Body.usesString opUses rest

/-! ### The declarations that name a map -/

mutual

/-- The printed type names a map type or a set type. -/
def Ty.usesMap : Ty T → Bool
  | .map .. | .set _ => true
  | .option t | .optional t | .list t => t.usesMap
  | .tuple ts | .app _ ts => Ty.usesMapList ts
  | .except e v => e.usesMap || v.usesMap
  | _ => false

def Ty.usesMapList : List (Ty T) → Bool
  | [] => false
  | t :: ts => t.usesMap || Ty.usesMapList ts

end

section
variable (onMap : E → Bool)

mutual

/-- `e` names a map or set type, or runs an operation that `onMap` says is on
maps or sets. -/
def Expr.usesMap : Expr T E → Bool
  | .ext op args => onMap op || Expr.usesMapList args
  | .call _ args | .tuple args => Expr.usesMapList args
  | .list elems t => Expr.usesMapList elems || t.usesMap
  | .struct fields _ args => Expr.usesMapFields fields || Ty.usesMapList args
  | .structUpdate base fields => base.usesMap || Expr.usesMapFields fields
  | .field a _ _ | .propNot a | .not a | .neg a | .isNone a | .isSome a
  | .decide a | .push _ a | .update _ _ a | .inject _ _ a | .proj a _ _ => a.usesMap
  | .ite a b c => a.usesMap || b.usesMap || c.usesMap
  | .matchNull _ a b | .coalesce a b _ | .intOp _ a b | .order _ a b | .division _ a b
  | .eq a b | .ne a b | .propAnd a b | .propOr a b | .and a b | .or a b => a.usesMap || b.usesMap
  | .ascribe e t => e.usesMap || t.usesMap
  | .listMethod _ items _ t body _ => items.usesMap || t.usesMap || body.usesMap
  | .listFold items init _ _ t body info =>
    items.usesMap || init.usesMap || t.usesMap || body.usesMap || info.result.usesMap
  | .int _ | .none | .bool _ | .string _ | .var _ | .enumCase .. | .tagValue _ => false

def Expr.usesMapList : List (Expr T E) → Bool
  | [] => false
  | e :: es => e.usesMap || Expr.usesMapList es

def Expr.usesMapFields : List (String × Expr T E) → Bool
  | [] => false
  | (_, e) :: fs => e.usesMap || Expr.usesMapFields fs

end

def Body.usesMap : Body T E → Bool
  | .value e | .exit e _ => e.usesMap onMap
  | .state _ | .yield .. | .done .. => false
  | .let _ e rest | .letTuple _ e rest => e.usesMap onMap || rest.usesMap
  | .letArray _ t elems rest => t.usesMap || Expr.usesMapList onMap elems || rest.usesMap
  | .ite c a b => c.usesMap onMap || a.usesMap || b.usesMap
  | .matchNull _ _ a b | .letState _ a b | .matchTag _ _ _ _ _ a b => a.usesMap || b.usesMap
  | .fold _ _ body items rest info =>
    body.usesMap || items.usesMap onMap || rest.usesMap ||
      info.stateTypes.any (·.usesMap) || info.elem.usesMap
  | .throw e => e.usesMap onMap
  | .bind _ _ args rest => Expr.usesMapList onMap args || rest.usesMap

/-- The output of `d` names a map or set type, or runs an operation on maps
or sets. A language imports its model of them then. -/
def Decl.usesMap : Decl T E → Bool
  | .struct _ _ fields | .tagged _ _ fields => fields.any (·.2.usesMap)
  | .alias _ _ type => type.usesMap
  | .enum .. => false
  | .function _ params ret body => params.any (·.2.usesMap) || ret.usesMap || body.usesMap onMap

end

section
variable (p : E → Bool)

mutual

/-- `e` runs an operation for which `p` holds. -/
def Expr.anyOp : Expr T E → Bool
  | .ext op args => p op || Expr.anyOpList args
  | .call _ args | .tuple args | .list args _ => Expr.anyOpList args
  | .struct fields _ _ => Expr.anyOpFields fields
  | .structUpdate base fields => base.anyOp || Expr.anyOpFields fields
  | .field a _ _ | .propNot a | .not a | .neg a | .isNone a | .isSome a
  | .decide a | .push _ a | .update _ _ a | .inject _ _ a | .proj a _ _ | .ascribe a _ => a.anyOp
  | .ite a b c => a.anyOp || b.anyOp || c.anyOp
  | .matchNull _ a b | .coalesce a b _ | .intOp _ a b | .order _ a b | .division _ a b
  | .eq a b | .ne a b | .propAnd a b | .propOr a b | .and a b | .or a b => a.anyOp || b.anyOp
  | .listMethod _ items _ _ body _ => items.anyOp || body.anyOp
  | .listFold items init _ _ _ body _ => items.anyOp || init.anyOp || body.anyOp
  | .int _ | .none | .bool _ | .string _ | .var _ | .enumCase .. | .tagValue _ => false

def Expr.anyOpList : List (Expr T E) → Bool
  | [] => false
  | e :: es => e.anyOp || Expr.anyOpList es

def Expr.anyOpFields : List (String × Expr T E) → Bool
  | [] => false
  | (_, e) :: fs => e.anyOp || Expr.anyOpFields fs

end

def Body.anyOp : Body T E → Bool
  | .value e | .exit e _ | .throw e => e.anyOp p
  | .state _ | .yield .. | .done .. => false
  | .let _ e rest | .letTuple _ e rest => e.anyOp p || rest.anyOp
  | .letArray _ _ elems rest => Expr.anyOpList p elems || rest.anyOp
  | .ite c a b => c.anyOp p || a.anyOp || b.anyOp
  | .matchNull _ _ a b | .letState _ a b | .matchTag _ _ _ _ _ a b => a.anyOp || b.anyOp
  | .fold _ _ body items rest _ => body.anyOp || items.anyOp p || rest.anyOp
  | .bind _ _ args rest => Expr.anyOpList p args || rest.anyOp

/-- The output of `d` runs an operation for which `p` holds. A language
imports the model that defines such operations then. -/
def Decl.anyOp : Decl T E → Bool
  | .function _ _ _ body => body.anyOp p
  | .struct .. | .tagged .. | .alias .. | .enum .. => false

end

/-- The output of `d` names the string type, or holds a string literal. A
language whose strings are not Lean's `String` imports its model then. -/
def Decl.usesString (opUses : E → Bool) : Decl T E → Bool
  | .struct _ _ fields => fields.any (·.2.usesString)
  | .alias _ _ type => type.usesString
  | .enum .. => false
  | .tagged _ _ members => members.any (·.2.usesString)
  | .function _ params ret body =>
    params.any (·.2.usesString) || ret.usesString || Body.usesString opUses body

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
  /-- Each `match` names the equation of its value `_h'`, as in
  `match _h' : x with`. The proof that a recursive function ends needs it, to
  know that a narrowed value is a part of the value it came from. No source
  name has a `'`, so `_h'` hides none, and Lean does not warn that the body
  leaves it unused, because it starts with `_`. -/
  matchHyp : Bool := false

/-- What the output writes after `match` and before the value. -/
def Names.matchBinder (names : Names) : String := if names.matchHyp then "_h' : " else ""

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
   ("some", "Option.some"), ("none", "Option.none"), ("Int", "Int"), ("Nat", "Nat"), ("Bool", "Bool"),
   ("String", "String"), ("DecidableEq", "DecidableEq"), ("Repr", "Repr"), ("Except", "Except")]

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
  /-- The string type. A language whose strings are not Lean's `String`
  writes its own, as TypeScript writes `JSString`. -/
  string : Names → String := fun names => leanName names "String"
  /-- The string literal `s`, written as a value of the string type. It may
  be an application, such as `JSString.ofString "a"`, so the printer puts it
  in parentheses where it is an argument. -/
  stringLit : Names → String → String := fun _ s => Sexp.quote s
  /-- The position `index`, a `Nat`, as a value of the type that the
  language gives the index of an array, such as `JSNumber.ofSafeInt` of it. -/
  indexValue : Names → String → String := fun names i => s!"({leanName names "Int"}.ofNat {i})"
  /-- A sort of the list `xs` by the comparator `fn`, a function of two
  elements, both as printed code. By default the comparator gives whether
  the first may come before the second, as `List.mergeSort` reads it. A
  language whose comparator gives a sign prints its own sort, as TypeScript
  prints `JSNumber.sortWith`. -/
  sortCall : Names → String → String → String := fun names fn xs =>
    s!"({leanName names "List.mergeSort"} {xs} {fn})"
  /-- The name of the type of a map that keeps its entries in insertion
  order, which takes the key type and the value type, such as `JSMap`. -/
  map : Names → String
  /-- The name of the type of a set that keeps its elements in insertion
  order, which takes the element type, such as `JSSet`. -/
  set : Names → String

/-- How a language prints the operations it adds, given its arguments as
printed code. -/
class PrintOp (E : Type) where
  print : Names → E → List String → String

mutual

def Ty.print [PrintTy T] (names : Names) : Ty T → String
  | .int => leanName names "Int"
  | .bool => leanName names "Bool"
  | .string => PrintTy.string (T := T) names
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
  | .tag _ => PrintTy.string (T := T) names
  | .tuple ts => "(" ++ " × ".intercalate (Ty.printList names ts) ++ ")"
  | .param name => name
  | .app ref args =>
    let (name, generic) := names.ref ref
    let number := if generic.isSome then s!" {names.typeParam}" else ""
    -- Each argument is one term: `List Int` needs its parentheses.
    let grouped := (Ty.printList names args).map fun a =>
      if a.contains ' ' && !a.startsWith "(" then s!"({a})" else a
    s!"({name}{number} {" ".intercalate grouped})"
  | .map k v =>
    let group (a : String) : String := if a.contains ' ' && !a.startsWith "(" then s!"({a})" else a
    s!"({PrintTy.map (T := T) names} {group (k.print names)} {group (v.print names)})"
  | .set t => wrapped (PrintTy.set (T := T) names) (t.print names)
  | .except e v =>
    let group (a : String) := if a.contains ' ' && !a.startsWith "(" then s!"({a})" else a
    s!"({leanName names "Except"} {group (e.print names)} {group (v.print names)})"
  | .ext t => PrintTy.print names t

def Ty.printList [PrintTy T] (names : Names) : List (Ty T) → List String
  | [] => []
  | t :: ts => t.print names :: Ty.printList names ts

end

mutual

/-- The printed type names the type parameter, so a declaration of it must
bind it. -/
def Ty.namesParam [PrintTy T] (names : Names) : Ty T → Bool
  | .struct ref | .tagged ref => (names.ref ref).2.isSome
  | .option t | .optional t | .list t => t.namesParam names
  | .tuple ts => Ty.namesParamList names ts
  | .app ref args => (names.ref ref).2.isSome || Ty.namesParamList names args
  | .map k v => k.namesParam names || v.namesParam names
  | .set t => t.namesParam names
  | .except e v => e.namesParam names || v.namesParam names
  | .ext t => PrintTy.namesParam names t
  | _ => false

def Ty.namesParamList [PrintTy T] (names : Names) : List (Ty T) → Bool
  | [] => false
  | t :: ts => t.namesParam names || Ty.namesParamList names ts

end

mutual

/-- The type parameters of a generic function that `t` names, in order. -/
def Ty.typeVars : Ty T → List String
  | .param name => [name]
  | .option t | .optional t | .list t => t.typeVars
  | .tuple ts | .app _ ts => Ty.typeVarsList ts
  | .map k v => k.typeVars ++ v.typeVars
  | .set t => t.typeVars
  | .except e v => e.typeVars ++ v.typeVars
  | _ => []

def Ty.typeVarsList : List (Ty T) → List String
  | [] => []
  | t :: ts => t.typeVars ++ Ty.typeVarsList ts

end

/-- How the output reads the element `index` of a tuple of `size` elements,
which Lean nests to the right: `.1`, `.2.1`, …, and `.2.2` for the last of
three. -/
def projPath (index size : Nat) : String :=
  String.join (List.replicate index ".2") ++ (if index + 1 < size then ".1" else "")

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
  | .let _ _ rest | .letArray _ _ _ rest | .letTuple _ _ rest => rest.testsTag name
  | .ite _ a b | .matchNull _ _ a b | .letState _ a b => a.testsTag name || b.testsTag name
  | .fold _ _ body _ rest _ => body.testsTag name || rest.testsTag name
  | .bind _ _ _ rest => rest.testsTag name
  | .value _ | .state _ | .yield .. | .done .. | .exit .. | .throw _ => false

/-! ### Recursion

A function of the output that calls itself must end, or Lean refuses it.
Tolean accepts a call of the function in its own body only on a part of one
of its parameters: a field of it, a value that a `match` narrows it to, an
element of a list in it, or a part of one of these. Each step makes the
value smaller by `sizeOf`, so `termination_by` the parameter holds, and the
tactic `tolean_decreasing` proves each call. These functions find that
parameter. -/

/-- How many steps below a parameter `p` an expression is, when `depths`
gives that number for each name that holds `p` or a part of it: `0` for `p`
itself, and `none` for a value that is not a part of `p`. Each step down
makes `sizeOf` smaller by one at least. A value that Lean wraps in `some` is
one step up, so a wrap of `p` itself is at `-1`. -/
def Expr.partOf (depths : List (String × Int)) : Expr T E → Option Int
  | .var x => depths.lookup x
  | .field e _ _ | .proj e _ _ => (e.partOf depths).map (· + 1)
  -- `(n : Option T)` may wrap a narrowed `n` in `some` again, which is one
  -- step up. The analysis does not know the type of `n`, so it counts the
  -- step even where `n` is an `Option` already, which only refuses more.
  | .ascribe e ty => (e.partOf depths).map fun d => if ty matches .option _ | .optional _ then d - 1 else d
  | _ => Option.none

/-- The depths after `x` is bound to a value at depth `d` below `p`. -/
def bindPart (depths : List (String × Int)) (x : String) (d : Option Int) : List (String × Int) :=
  let depths := depths.filter (·.1 != x)
  match d with
  | some d => (x, d) :: depths
  | Option.none => depths

/-- The depths after a `match` narrows `x`, which is one step down. -/
def narrowPart (depths : List (String × Int)) (x : String) : List (String × Int) :=
  match depths.lookup x with
  | some d => bindPart depths x (some (d + 1))
  | Option.none => depths

/-- An argument without its ascription to an `Option` type, such as the
`(v : Option T)` that the translator writes for an optional parameter of a
generic function. A parameter of an `Option` type already needs a part two
steps below it, for the `some` that Lean may add, and the ascription adds
that `some` in its place, not as well. -/
def Expr.unascribed : Expr T E → Expr T E
  | .ascribe e ty => if ty matches .option _ | .optional _ then e else .ascribe e ty
  | e => e

mutual

/-- Each call of `self` in the expression passes as its argument `i` a part
of `p` at least `need` steps below it. -/
def Expr.callsShrink (self : DeclRef) (i : Nat) (need : Int) (depths : List (String × Int)) : Expr T E → Bool
  | .call r args =>
    (r != self || (args[i]?.bind fun a => a.unascribed.partOf depths).any (need ≤ ·)) &&
      Expr.callsShrinkList self i need depths args
  | .listMethod method items param _ body _ =>
    let elemPart := (items.partOf depths).map (· + 1)
    -- A comparator's second parameter is an element too.
    let inner := match method with
      | .sortWith other => bindPart (bindPart depths other elemPart) param elemPart
      | _ => bindPart depths param elemPart
    items.callsShrink self i need depths && body.callsShrink self i need inner
  -- The accumulator is not a part of `p`, and the element is one step below
  -- `items`, as in a `listMethod`.
  | .listFold items init acc param _ body _ =>
    items.callsShrink self i need depths && init.callsShrink self i need depths &&
      body.callsShrink self i need
        (bindPart (bindPart depths acc Option.none) param ((items.partOf depths).map (· + 1)))
  | .matchNull name whenNull whenValue =>
    whenNull.callsShrink self i need depths && whenValue.callsShrink self i need (narrowPart depths name)
  | .field e _ _ | .propNot e | .not e | .neg e | .isNone e | .isSome e | .inject _ _ e
  | .decide e | .push _ e | .update _ _ e | .ascribe e _ | .proj e _ _ => e.callsShrink self i need depths
  | .ite a b c => a.callsShrink self i need depths && b.callsShrink self i need depths &&
      c.callsShrink self i need depths
  | .coalesce a b _ | .intOp _ a b | .order _ a b | .division _ a b | .eq a b | .ne a b
  | .propAnd a b | .propOr a b | .and a b | .or a b =>
    a.callsShrink self i need depths && b.callsShrink self i need depths
  | .list es _ | .tuple es | .ext _ es => Expr.callsShrinkList self i need depths es
  | .struct fields _ _ => Expr.callsShrinkFields self i need depths fields
  | .structUpdate base fields =>
    base.callsShrink self i need depths && Expr.callsShrinkFields self i need depths fields
  | .int _ | .none | .bool _ | .string _ | .var _ | .enumCase .. | .tagValue _ => true

def Expr.callsShrinkList (self : DeclRef) (i : Nat) (need : Int) (depths : List (String × Int)) :
    List (Expr T E) → Bool
  | [] => true
  | e :: es => e.callsShrink self i need depths && Expr.callsShrinkList self i need depths es

def Expr.callsShrinkFields (self : DeclRef) (i : Nat) (need : Int) (depths : List (String × Int)) :
    List (String × Expr T E) → Bool
  | [] => true
  | (_, e) :: fs => e.callsShrink self i need depths && Expr.callsShrinkFields self i need depths fs

end

/-- The depths after `names` get new values that are not parts of `p`. -/
def forgetParts (depths : List (String × Int)) (names : List String) : List (String × Int) :=
  depths.filter (!names.contains ·.1)

/-- Each call of `self` in the body passes as its argument `i` a part of `p`
at least `need` steps below it. -/
def Body.callsShrink (self : DeclRef) (i : Nat) (need : Int) (depths : List (String × Int)) : Body T E → Bool
  | .value e | .exit e _ => e.callsShrink self i need depths
  | .state _ | .yield .. | .done .. => true
  | .let name e rest =>
    e.callsShrink self i need depths && rest.callsShrink self i need (bindPart depths name (e.partOf depths))
  | .letArray name _ elems rest =>
    Expr.callsShrinkList self i need depths elems &&
      rest.callsShrink self i need (bindPart depths name Option.none)
  | .ite c a b => c.callsShrink self i need depths && a.callsShrink self i need depths &&
      b.callsShrink self i need depths
  | .matchNull name _ whenNull whenValue =>
    whenNull.callsShrink self i need depths && whenValue.callsShrink self i need (narrowPart depths name)
  | .matchTag name _ _ _ other whenTag whenOther =>
    whenTag.callsShrink self i need (narrowPart depths name) &&
      whenOther.callsShrink self i need (if other.isSome then narrowPart depths name else depths)
  | .letState names branch rest =>
    branch.callsShrink self i need depths && rest.callsShrink self i need (forgetParts depths names)
  | .letTuple names e rest =>
    e.callsShrink self i need depths && rest.callsShrink self i need (forgetParts depths names)
  | .fold names element body items rest _ =>
    let outer := forgetParts depths names
    items.callsShrink self i need depths &&
      body.callsShrink self i need (bindPart outer element ((items.partOf depths).map (· + 1))) &&
      rest.callsShrink self i need outer
  | .throw e => e.callsShrink self i need depths
  -- The value of a call is not a part of `p`.
  | .bind name r args rest =>
    (Expr.call r args).callsShrink self i need depths &&
      rest.callsShrink self i need (bindPart depths name Option.none)

mutual

/-- The expression calls `self`. -/
def Expr.calls (self : DeclRef) : Expr T E → Bool
  | .call r args => r == self || Expr.callsList self args
  | .listMethod _ items _ _ body _ => items.calls self || body.calls self
  | .listFold items init _ _ _ body _ => items.calls self || init.calls self || body.calls self
  | .matchNull _ a b | .coalesce a b _ | .intOp _ a b | .order _ a b | .division _ a b | .eq a b
  | .ne a b | .propAnd a b | .propOr a b | .and a b | .or a b => a.calls self || b.calls self
  | .field e _ _ | .propNot e | .not e | .neg e | .isNone e | .isSome e | .inject _ _ e
  | .decide e | .push _ e | .update _ _ e | .ascribe e _ | .proj e _ _ => e.calls self
  | .ite a b c => a.calls self || b.calls self || c.calls self
  | .list es _ | .tuple es | .ext _ es => Expr.callsList self es
  | .struct fields _ _ => Expr.callsFields self fields
  | .structUpdate base fields => base.calls self || Expr.callsFields self fields
  | .int _ | .none | .bool _ | .string _ | .var _ | .enumCase .. | .tagValue _ => false

def Expr.callsList (self : DeclRef) : List (Expr T E) → Bool
  | [] => false
  | e :: es => e.calls self || Expr.callsList self es

def Expr.callsFields (self : DeclRef) : List (String × Expr T E) → Bool
  | [] => false
  | (_, e) :: fs => e.calls self || Expr.callsFields self fs

end

/-- The body calls `self`. -/
def Body.calls (self : DeclRef) : Body T E → Bool
  | .value e | .exit e _ => e.calls self
  | .state _ | .yield .. | .done .. => false
  | .let _ e rest | .letTuple _ e rest => e.calls self || rest.calls self
  | .letArray _ _ elems rest => Expr.callsList self elems || rest.calls self
  | .ite c a b => c.calls self || a.calls self || b.calls self
  | .matchNull _ _ a b | .matchTag _ _ _ _ _ a b | .letState _ a b => a.calls self || b.calls self
  | .fold _ _ body items rest _ => body.calls self || items.calls self || rest.calls self
  | .throw e => e.calls self
  | .bind _ r args rest => r == self || Expr.callsList self args || rest.calls self

/-- The parameter that each call of `self` in `body` makes smaller, the first
one when there are several. `none` when the body does not call `self`, or
when no parameter gets smaller in every call. A parameter of an `Option` type
needs a part two steps below it. Where such a parameter expects a value that
a `match` narrowed, Lean wraps the value in `some` again, which is one step
up, so a part one step below would be the parameter itself. -/
def Body.decreasingParam? (self : DeclRef) (params : List (String × Ty T)) (body : Body T E) :
    Option String :=
  if body.calls self then
    (params.zipIdx.find? fun ((p, ty), i) =>
      body.callsShrink self i (if ty matches .option _ | .optional _ then 2 else 1) [(p, 0)]).map (·.1.1)
  else Option.none

/-- The declaration is a function of the file `file` that calls itself, each
time on a part of one parameter. The output then proves that it ends with
`tolean.TypeScript.Decreasing`. -/
def Decl.recursive (file : String) : Decl T E → Bool
  | .function name params _ body => (body.decreasingParam? ⟨file, name⟩ params).isSome
  | _ => false

section
variable [PrintTy T] [PrintOp E]

/-- The type of a loop's state, such as `Int × Bool`. -/
def foldState (names : Names) (info : LoopInfo T) : String :=
  " × ".intercalate (info.stateTypes.map (·.print names))

/-- The state of one step of a loop: the tuple of `names`, after `slot`, the
value to return, in a loop that a `return` can end. -/
def stepTuple (slot : Option String) (names : List String) : String :=
  match slot with
  | some s => if names.isEmpty then s else s!"({s}, {", ".intercalate names})"
  | Option.none => tuple names

/-- The binders of the function that `List.foldl` runs for a loop, with their
types: `((x, y) : Int × Bool) (e : T)`. Lean elaborates the body before it
knows the types, so in `{ f := e }` with a field of type `Option N` it would
take `e` to be an `Option N`, not an `N` to wrap. `forIn` passes the element
first, so a loop that a `break` can end has the binders the other way round. -/
def foldBinders (names : Names) (state : List String) (element : String) (info : LoopInfo T) :
    String :=
  let stateBinder := match info.returns with
    | some r =>
      let slotTy := (Ty.option r).print names
      if state.isEmpty then s!"(_ : {slotTy})"
      else s!"({stepTuple (some "_") state} : {slotTy} × {foldState names info})"
    | Option.none => s!"({tuple state} : {foldState names info})"
  let elementBinder := s!"({element} : {info.elem.print names})"
  if info.breaks then s!"{elementBinder} {stateBinder}" else s!"{stateBinder} {elementBinder}"

mutual

def Expr.print (names : Names) : Expr T E → String
  | .int n => s!"({n} : {leanName names "Int"})"
  | .none => leanName names "none"
  | .ascribe e t => s!"({e.print names} : {t.print names})"
  | .listMethod method items param elem body _ =>
    let fn := s!"(fun ({param} : {elem.print names}) => {body.print names})"
    let xs := argument (items.print names)
    match method with
    | .map => s!"({leanName names "List.map"} {fn} {xs})"
    | .filter => s!"({leanName names "List.filter"} {fn} {xs})"
    | .any => s!"({leanName names "List.any"} {xs} {fn})"
    | .all => s!"({leanName names "List.all"} {xs} {fn})"
    | .find => s!"({leanName names "List.find?"} {fn} {xs})"
    | .mapIdx index =>
      -- The function takes the position as a `Nat` and binds it again under
      -- the same name, as a value of the type the language gives an index.
      let value := PrintTy.indexValue (T := T) names index
      let fn := s!"(fun ({index} : {leanName names "Nat"}) ({param} : {elem.print names}) => " ++
        s!"let {index} := {value}; {body.print names})"
      s!"({leanName names "List.mapIdx"} {fn} {xs})"
    | .findIndex =>
      -- The position of the first element that passes, or `-1`.
      let int := leanName names "Int"
      PrintTy.indexValue (T := T) names
        s!"((({leanName names "List.findIdx?"} {fn} {xs}).map {int}.ofNat).getD (-1))"
    | .findLast => s!"({leanName names "List.find?"} {fn} ({leanName names "List.reverse"} {xs}))"
    | .sortWith other =>
      let elemTy := elem.print names
      PrintTy.sortCall (T := T) names
        s!"(fun ({param} : {elemTy}) ({other} : {elemTy}) => {body.print names})" xs
  | .listFold items init acc param elem body info =>
    let fn := s!"(fun ({acc} : {info.result.print names}) ({param} : {elem.print names}) => {body.print names})"
    s!"({leanName names "List.foldl"} {fn} {argument (init.print names)} {argument (items.print names)})"
  | .structUpdate base fields =>
    if fields.isEmpty then base.print names
    else
      let sets := ", ".intercalate (Expr.printFields names fields)
      s!"\{ {argument (base.print names)} with {sets} }"
  | .bool b => if b then "true" else "false"
  | .string s => PrintTy.stringLit (T := T) names s
  | .var name => name
  | .enumCase ref member => s!"{(names.ref ref).1}.{memberName member}"
  | .tagValue value => PrintTy.stringLit (T := T) names value
  | .inject ref tag e =>
    -- The constructor gets the type parameter by name, as a call does. A
    -- value such as `(1 : Int)` does not mention the parameter, so Lean
    -- could not infer it.
    let head := match names.ref ref with
      | (name, some binder) => s!"{name}.{memberName tag} ({binder} := {names.typeParam})"
      | (name, Option.none) => s!"{name}.{memberName tag}"
    s!"({head} {argument (e.print names)})"
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
  | .struct fields ref args =>
    let type : Ty T := if args.isEmpty then .struct ref else .app ref args
    "({ " ++ ", ".intercalate (Expr.printFields names fields) ++ " } : " ++ type.print names ++ ")"
  | .isNone a => s!"{argument (a.print names)}.isNone"
  | .isSome a => s!"{argument (a.print names)}.isSome"
  | .matchNull name whenNull whenValue =>
    s!"(match {names.matchBinder}{name} with | {leanName names "none"} => {whenNull.print names} | " ++
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
  | .tuple es => "(" ++ ", ".intercalate (Expr.printList names es) ++ ")"
  | .proj e index size => argument (e.print names) ++ projPath index size

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
  | .yield ns slot =>
    [wrapped (leanName names "ForInStep.yield")
      (stepTuple (if slot then some (leanName names "none") else Option.none) ns)]
  | .done ns slot =>
    [wrapped (leanName names "ForInStep.done")
      (stepTuple (if slot then some (leanName names "none") else Option.none) ns)]
  | .exit e ns =>
    [wrapped (leanName names "ForInStep.done")
      (stepTuple (some (wrapped (leanName names "some") (e.print names))) ns)]
  | .let name e rest => s!"let {name} := {e.print names}" :: rest.lines names
  | .letTuple ns e rest => s!"let {tuple ns} := {e.print names}" :: rest.lines names
  | .letArray name type elems rest =>
    s!"let {name} : {type.print names} := [{", ".intercalate (Expr.printList names elems)}]" ::
      rest.lines names
  | .ite c whenTrue whenFalse =>
    [s!"if {c.print names} then"] ++ indent (whenTrue.lines names) ++ ["else"] ++
      indent (whenFalse.lines names)
  | .matchNull name _ whenNull whenValue =>
    [s!"match {names.matchBinder}{name} with", s!"| {leanName names "none"} =>"] ++ indent (whenNull.lines names) ++
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
    s!"match {names.matchBinder}{name} with" :: s!"| {ctor tag} {name} =>" :: indent (whenTag.lines names) ++ rest
  | .letState ns branch rest =>
    [s!"let {tuple ns} :="] ++ indent (branch.lines names) ++ rest.lines names
  | .fold ns element body items rest info =>
    let bodyLines := body.lines names
    let lastLine := bodyLines.getLast?.getD ""
    if info.returns.isSome then
      let none_ := leanName names "none"
      [s!"match {leanName names "Id.run"} ({leanName names "forIn"} {items.print names} {stepTuple (some none_) ns}",
        s!"    (fun {foldBinders names ns element info} =>"] ++
        indentBy "      " (bodyLines.dropLast ++ [lastLine ++ ")) with"]) ++
        [s!"| {stepTuple (some s!"{leanName names "some"} r") (if ns.isEmpty then [] else ["_"])} => r",
          s!"| {stepTuple (some none_) ns} =>"] ++ indent (rest.lines names)
    else if info.breaks then
      [s!"let {tuple ns} :=",
        s!"  {leanName names "Id.run"} ({leanName names "forIn"} {items.print names} {tuple ns}",
        s!"    (fun {foldBinders names ns element info} =>"] ++
        indentBy "      " (bodyLines.dropLast ++ [lastLine ++ "))"]) ++ rest.lines names
    else
      [s!"let {tuple ns} :=", s!"  {leanName names "List.foldl"}",
        s!"    (fun {foldBinders names ns element info} =>"] ++
        indentBy "      " (bodyLines.dropLast ++ [lastLine ++ ")"]) ++
        [s!"    {tuple ns} {items.print names}"] ++ rest.lines names
  | .throw e => [wrapped "throw" (e.print names)]
  | .bind name ref args rest =>
    s!"{(Expr.call ref args).print names} >>= fun {name} =>" :: rest.lines names

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
  | .struct name typeParams fields =>
    let generic := if names.generic then s!" ({names.typeParam} : Type)" else ""
    let generic := generic ++ String.join (typeParams.map (s!" ({·} : Type)"))
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
  | .alias name typeParams type =>
    let generic := if type.namesParam names then s!" ({names.typeParam} : Type)" else ""
    let generic := generic ++ String.join (typeParams.map (s!" ({·} : Type)"))
    s!"abbrev {name}{generic} := {type.print names}"
  | .function name params ret body =>
    -- A function that calls itself ends because each call passes a part of
    -- one parameter. Lean then needs that parameter as the measure, and the
    -- proof of each call.
    let decreasing := body.decreasingParam? ⟨names.file, name⟩ params
    let names := if decreasing.isSome then { names with matchHyp := true } else names
    let termination := match decreasing with
      | some p => [s!"termination_by {p}", "decreasing_by all_goals tolean_decreasing"]
      | Option.none => []
    let generic := if names.generic then PrintTy.binders (T := T) names else ""
    -- The type parameters, in the order that the parameters name them. The
    -- translator refuses one that no parameter's type names.
    let vars := (Ty.typeVarsList (params.map (·.2) ++ [ret])).eraseDups
    let generic := if vars.isEmpty then generic else generic ++ " {" ++ " ".intercalate vars ++ " : Type}"
    -- An optional parameter defaults to `none`, so that a claim may leave
    -- it out, as a call in the source may.
    let leanParams := params.map fun (param, type) =>
      let default := if type matches .optional _ then s!" := {leanName names "none"}" else ""
      s!"({param} : {type.print names}{default})"
    "\n".intercalate
      (s!"def {name}{generic} {" ".intercalate leanParams} : {ret.print names} :=" ::
        indent (body.lines names) ++ termination)

end

end tolean.IR
