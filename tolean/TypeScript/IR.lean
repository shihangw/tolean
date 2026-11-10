import tolean.IR

/-!
The TypeScript extension of the Tolean IR: the types and operations that the
TypeScript translator adds to the shared IR in `tolean/IR.lean`.

TypeScript adds the number type of the abstract number model `JSNumber`, and
`Option Empty` as the type of `null` alone. It adds the operations of the
number model, such as `JSNumber.add`. `Ty`, `Expr`, `Body` and `Decl` here
are the shared types with these added, and definitions such as
`Expr.numberOp` name each added form, so that code and proofs can match on
it as on a constructor.

`IR/Eval.lean` gives the IR a meaning, so that a theorem can state what the
translator writes for every program it accepts.
-/
namespace tolean.TypeScript.IR

export tolean.IR (IntOp Order Division Names ImportedFile leanReserved memberName)

/-- An operation of the abstract number model `JSNumber` on two numbers. -/
inductive NumberOp where
  | add | sub | mul | lt | le | eq
deriving BEq, Repr, Inhabited, DecidableEq

/-- A constant of the number model. -/
inductive NumberConstant where
  | nan | posInf | negInf
deriving BEq, Repr, Inhabited, DecidableEq

/-- A test of the number model on one number. -/
inductive NumberTest where
  | isSafeInteger | isNaN | isFinite
deriving BEq, Repr, Inhabited, DecidableEq

/-- The types that TypeScript adds to the IR. -/
inductive TyExt where
  /-- The number type parameter, `N`. -/
  | number
  /-- `Option Empty`, the type of `null` alone. -/
  | null
  /-- `JSError`, what `throw new Error(message)` throws. -/
  | error
deriving BEq, Repr, Inhabited, DecidableEq

/-- The operations that TypeScript adds to the IR, each with the number of
arguments it takes. -/
inductive ExprExt where
  /-- `(JSNumber.ofSafeInt (N := N) (n : Int))`, on no arguments. -/
  | number (n : Int)
  /-- `(JSNumber.nan (N := N))`, on no arguments. -/
  | numberConstant (c : NumberConstant)
  /-- `(JSNumber.neg a)`. -/
  | numberNeg
  /-- `(JSNumber.add a b)`. -/
  | numberOp (op : NumberOp)
  /-- `!(JSNumber.eq a b)`. -/
  | numberNe
  /-- `(JSNumber.isNaN a)`, or `(JSNumber.toSafeInt a).isSome`. -/
  | numberTest (test : NumberTest)
  /-- `none`, on no arguments, as an optional value: `undefined`, such as
  the argument of an optional parameter that a call leaves out. -/
  | undefined
  /-- `a.isNone`, on an optional value: `a === undefined`. -/
  | isUndefined
  /-- `a.isSome`, on an optional value: `a !== undefined`. -/
  | isDefined
  /-- `a.map (·.f.g)`, or `a.bind (·.f.g)` when the last field is optional:
  `a?.f.g`, which is `undefined` when `a` is `null` or `undefined`. The
  fields before the last are required. -/
  | optField (path : List String) (bind : Bool)
  /-- `match k with | K.a => r.a | …`, on `r` and `k`: `r[k]`, where `r` is a
  `Record<K, V>` with the keys `keys`, and `K` is the literal union `key`. -/
  | recordGet (key : DeclRef) (keys : List String)
  /-- `JSMap.empty`, on no arguments: `new Map()`. The translator writes the
  type of the map after it. -/
  | mapEmpty
  /-- `(JSMap.get? m k)`: `m.get(k)`, which is `undefined` when `m` has no
  key `k`. -/
  | mapGet
  /-- `(JSMap.has m k)`: `m.has(k)`. -/
  | mapHas
  /-- `(JSNumber.ofSafeInt (JSMap.size m : Int))`: `m.size`, a number. -/
  | mapSize
  /-- `(JSMap.set m k v)`: the map after `m.set(k, v)`. -/
  | mapSet
  /-- `(JSMap.delete m k)`: the map after `m.delete(k)`. -/
  | mapDelete
  /-- `JSSet.empty`, on no arguments: `new Set()`. The translator writes the
  type of the set after it. -/
  | setEmpty
  /-- `(JSSet.has s x)`: `s.has(x)`. -/
  | setHas
  /-- `(JSNumber.ofSafeInt (JSSet.size s : Int))`: `s.size`, a number. -/
  | setSize
  /-- `(JSSet.add s x)`: the set after `s.add(x)`. -/
  | setAdd
  /-- `(JSSet.delete s x)`: the set after `s.delete(x)`. -/
  | setDelete
  /-- `(pure a)`: the value `a` as the result of a function that can throw. -/
  | pure
  /-- `(JSError.mk m)`: the error that `new Error(m)` makes, from its message. -/
  | error
deriving BEq, Repr, Inhabited, DecidableEq

/-- An operation on maps or sets, whose output names `JSMap` or `JSSet`. -/
def ExprExt.onMap : ExprExt → Bool
  | .mapEmpty | .mapGet | .mapHas | .mapSize | .mapSet | .mapDelete => true
  | .setEmpty | .setHas | .setSize | .setAdd | .setDelete => true
  | _ => false

abbrev Ty := tolean.IR.Ty TyExt
abbrev Expr := tolean.IR.Expr TyExt ExprExt
abbrev Body := tolean.IR.Body TyExt ExprExt
abbrev Decl := tolean.IR.Decl TyExt ExprExt
abbrev LoopInfo := tolean.IR.LoopInfo TyExt

/-- The number type parameter, `N`. -/
@[match_pattern] abbrev Ty.number : Ty := .ext .number
/-- `Option Empty`, the type of `null` alone. -/
@[match_pattern] abbrev Ty.null : Ty := .ext .null

@[match_pattern] abbrev Expr.number (n : Int) : Expr := .ext (.number n) []
@[match_pattern] abbrev Expr.numberConstant (c : NumberConstant) : Expr :=
  .ext (.numberConstant c) []
@[match_pattern] abbrev Expr.numberNeg (a : Expr) : Expr := .ext .numberNeg [a]
@[match_pattern] abbrev Expr.numberOp (op : NumberOp) (a b : Expr) : Expr :=
  .ext (.numberOp op) [a, b]
@[match_pattern] abbrev Expr.numberNe (a b : Expr) : Expr := .ext .numberNe [a, b]
@[match_pattern] abbrev Expr.numberTest (test : NumberTest) (a : Expr) : Expr :=
  .ext (.numberTest test) [a]
@[match_pattern] abbrev Expr.undefined : Expr := .ext .undefined []
@[match_pattern] abbrev Expr.isUndefined (a : Expr) : Expr := .ext .isUndefined [a]
@[match_pattern] abbrev Expr.isDefined (a : Expr) : Expr := .ext .isDefined [a]
@[match_pattern] abbrev Ty.error : Ty := .ext .error
@[match_pattern] abbrev Expr.pure (a : Expr) : Expr := .ext .pure [a]
@[match_pattern] abbrev Expr.error (message : Expr) : Expr := .ext .error [message]

/-! ### Printing -/

/-- The Lean names the output uses, with their full names from the root. -/
def leanNames : List (String × String) :=
  tolean.IR.leanNames ++
    [("JSNumber", "tolean.TypeScript.JSNumber"), ("JSString", "tolean.TypeScript.JSString"),
     ("JSMap", "tolean.TypeScript.JSMap"), ("JSSet", "tolean.TypeScript.JSSet"),
     ("JSError", "tolean.TypeScript.JSError"), ("pure", "Pure.pure")]

/-- Write the Lean name `name` (or `name.rest`), from the root when the source
declares the same name. -/
def leanName (names : Names) (name : String) : String :=
  tolean.IR.leanNameIn leanNames names name

def NumberOp.name : NumberOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .lt => "lt" | .le => "le" | .eq => "eq"

def NumberConstant.name : NumberConstant → String
  | .nan => "nan" | .posInf => "posInf" | .negInf => "negInf"

instance : tolean.IR.PrintTy TyExt where
  print names
    | .number => names.typeParam
    | .null => s!"({leanName names "Option"} Empty)"
    | .error => leanName names "JSError"
  namesParam _
    | .number => true
    | .null | .error => false
  binders names :=
    let n := names.typeParam
    s!" \{{n} : Type} [{leanName names "JSNumber"} {n}]"
  -- A JS string is a list of UTF-16 code units, not a Lean `String`
  -- (`Spec/String.lean`), and a literal encodes its text.
  string names := leanName names "JSString"
  -- A JS `Map` keeps its entries in insertion order (`tolean/TypeScript/Map.lean`).
  map names := leanName names "JSMap"
  set names := leanName names "JSSet"
  stringLit names s := s!"{leanName names "JSString.ofString"} {tolean.Sexp.quote s}"

open tolean.IR (argument) in
/-- An operation on its printed arguments. The translator gives each one the
number of arguments it takes, and the printer writes nothing more for others. -/
def ExprExt.print (names : Names) (op : ExprExt) (args : List String) : String :=
  let js := leanName names "JSNumber"
  match op, args with
  | .number n, _ =>
    s!"({js}.ofSafeInt (N := {names.typeParam}) ({n} : {leanName names "Int"}))"
  | .numberConstant c, _ => s!"({js}.{c.name} (N := {names.typeParam}))"
  | .numberNeg, [a] => s!"({js}.neg {argument a})"
  | .numberOp op, [a, b] => s!"({js}.{op.name} {argument a} {argument b})"
  | .numberNe, [a, b] => s!"!({js}.eq {argument a} {argument b})"
  | .numberTest .isSafeInteger, [a] => s!"({js}.toSafeInt {argument a}).isSome"
  | .numberTest .isNaN, [a] => s!"({js}.isNaN {argument a})"
  | .numberTest .isFinite, [a] => s!"({js}.isFinite {argument a})"
  | .undefined, _ => leanName names "none"
  | .isUndefined, [a] => s!"{argument a}.isNone"
  | .isDefined, [a] => s!"{argument a}.isSome"
  | .optField path bind, [a] =>
    s!"({argument a}.{if bind then "bind" else "map"} (·.{".".intercalate path}))"
  | .mapEmpty, _ => s!"{leanName names "JSMap"}.empty"
  | .mapGet, [m, k] => s!"({leanName names "JSMap"}.get? {argument m} {argument k})"
  | .mapHas, [m, k] => s!"({leanName names "JSMap"}.has {argument m} {argument k})"
  | .mapSize, [m] =>
    s!"({js}.ofSafeInt (N := {names.typeParam}) ({leanName names "JSMap"}.size {argument m} : {leanName names "Int"}))"
  | .mapSet, [m, k, v] => s!"({leanName names "JSMap"}.set {argument m} {argument k} {argument v})"
  | .mapDelete, [m, k] => s!"({leanName names "JSMap"}.delete {argument m} {argument k})"
  | .setEmpty, _ => s!"{leanName names "JSSet"}.empty"
  | .setHas, [s, x] => s!"({leanName names "JSSet"}.has {argument s} {argument x})"
  | .setSize, [s] =>
    s!"({js}.ofSafeInt (N := {names.typeParam}) ({leanName names "JSSet"}.size {argument s} : {leanName names "Int"}))"
  | .setAdd, [s, x] => s!"({leanName names "JSSet"}.add {argument s} {argument x})"
  | .setDelete, [s, x] => s!"({leanName names "JSSet"}.delete {argument s} {argument x})"
  | .recordGet key keys, [r, k] =>
    let case (f : String) := s!"{(names.ref key).1}.{memberName f}"
    -- A key that is one constructor, as `r['a']` gives, reads its field.
    match keys.find? (case · == k) with
    | some f => s!"{argument r}.{f}"
    | Option.none =>
      s!"(match {k} with{String.join (keys.map fun f => s!" | {case f} => {argument r}.{f}")})"
  | .pure, [a] => s!"({tolean.IR.wrapped (leanName names "pure") a})"
  | .error, [m] => s!"({tolean.IR.wrapped (leanName names "JSError.mk") m})"
  | _, _ => ""

instance : tolean.IR.PrintOp ExprExt := ⟨ExprExt.print⟩

end tolean.TypeScript.IR
