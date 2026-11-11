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

/-- How one operand of `a + b` on strings becomes a string, by ToString: a
string stays itself, and a bigint or a boolean becomes its text. -/
inductive StringPart where
  | string | bigint | boolean
deriving BEq, Repr, Inhabited, DecidableEq

/-- A method of a string that the subset has. -/
inductive StringMethod where
  | startsWith | endsWith | includes | indexOf | trim | trimStart | trimEnd | split
deriving BEq, Repr, Inhabited, DecidableEq

def StringMethod.name : StringMethod → String
  | .startsWith => "startsWith" | .endsWith => "endsWith" | .includes => "includes"
  | .indexOf => "indexOf" | .trim => "trim" | .trimStart => "trimStart" | .trimEnd => "trimEnd"
  | .split => "split"

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
  /-- `(JSString.lt a b)`, or `(JSString.le a b)` when `le` is true: `a < b`
  or `a <= b` on strings. The translator swaps the operands for `>` and
  `>=`. -/
  | stringOrder (le : Bool)
  /-- `(a ++ b)`, where `left` and `right` say how each operand becomes a
  string, such as `(a ++ JSString.ofInt b)`: `a + b` where one operand is a
  string. -/
  | stringAppend (left right : StringPart)
  /-- `(JSNumber.ofSafeInt (N := N) ((JSString.length s : Nat) : Int))`, on
  `s`: `s.length`, the number of code units. -/
  | stringLength
  /-- `(JSString.startsWith s p)`, or the other method, on `s` and the
  arguments: `s.startsWith(p)`. `indexOf` gives an index, which the output
  makes a number: `(JSNumber.ofSafeInt (N := N) (JSString.indexOf s p))`. -/
  | stringMethod (method : StringMethod)
  /-- `(JSString.codePoints s)`, on `s`: the strings that `for (const c of s)`
  and `[...s]` visit, one for each code point. -/
  | stringCodePoints
  /-- `match k with | K.a => r.a | …`, on `r` and `k`: `r[k]`, where `r` is a
  `Record<K, V>` with the keys `keys`, and `K` is the literal union `key`. -/
  | recordGet (key : DeclRef) (keys : List String)
  /-- `x ∈ xs`, a `Prop`, on `xs` and `x`: `xs.includes(x)`, where the
  elements are integers, booleans, strings or constructors of a literal
  union, which SameValueZero compares as `=` does. -/
  | includes
  /-- `(List.any xs (JSNumber.sameValueZero x))`, on `xs` and `x`:
  `xs.includes(x)` on numbers, where `NaN` is the same as `NaN`. -/
  | includesNumber
  /-- `(JSNumber.ofSafeInt (N := N) (List.length xs : Int))`, on `xs`:
  `xs.length`. -/
  | length
  /-- `xs[k]?`, on `xs`: `xs[k]` with a number literal `k`, which is the
  element at `k` or `undefined`. -/
  | indexLit (k : Nat)
  /-- `(JSNumber.elementAt? xs i)`, on `xs` and `i`: `xs[i]` with a number
  `i`. -/
  | indexNumber
  /-- `(JSNumber.countUp (k : Int) b)`, on `b`: the values of `i` in
  `for (let i = k; i < b; i++)`. -/
  | countUp (k : Int)
  /-- `xs[k]?`, or `(List.reverse xs)[-k - 1]?` when `k` is negative, on
  `xs`: `xs.at(k)` with an integer literal `k`. -/
  | at (k : Int)
  /-- `List.take` and `List.drop` on `xs`, with `List.reverse` for a negative
  bound: `xs.slice(start, stop)` with integer literals. A negative `start`
  with a `stop` that is not negative is not one of them. -/
  | slice (start : Int) (stop : Option Int)
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
  /-- `s.elems`: the elements of a set, which `for (const x of s)` visits. -/
  | setElems
  /-- `m.entries`: the entries of a map, which `for (const e of m)` visits,
  each as a pair. -/
  | mapEntries
  /-- `(JSMap.ofList xs)`: `new Map(items)`, where the output's `xs` is the
  list of pairs that `items` visits. The translator writes the type after it. -/
  | mapOfList
  /-- `(JSSet.ofList xs)`: `new Set(items)`, in the same way. -/
  | setOfList
  /-- `(a ++ b ++ c)`, on one list or more, and `a` alone on one: an array
  literal with a spread, such as `[...xs, x]`, which is `xs ++ [x]`. -/
  | append
  /-- `(pure a)`: the value `a` as the result of a function that can throw. -/
  | pure
  /-- `(JSError.mk m)`: the error that `new Error(m)` makes, from its message. -/
  | error
deriving BEq, Repr, Inhabited, DecidableEq

/-- An operation on maps or sets, whose output names `JSMap` or `JSSet`. -/
def ExprExt.onMap : ExprExt → Bool
  | .mapEmpty | .mapGet | .mapHas | .mapSize | .mapSet | .mapDelete => true
  | .setEmpty | .setHas | .setSize | .setAdd | .setDelete | .setElems | .mapEntries => true
  | .mapOfList | .setOfList => true
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
     ("JSError", "tolean.TypeScript.JSError"), ("pure", "Pure.pure"),
     ("Nat", "Nat")]

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
  -- The index that `Array.prototype.map` passes is a number (ECMA-262
  -- §23.1.3.21), and an array has fewer than 2^32 elements, so the index is a
  -- safe integer.
  indexValue names i :=
    s!"({leanName names "JSNumber"}.ofSafeInt (N := {names.typeParam}) ({i} : {leanName names "Int"}))"

/-- Whether one pair of parentheses holds all of `code`, as in `(f x)` but not
in `(a) ++ (b)`. A parenthesis in a string literal does not count. -/
def wholeParens (code : String) : Bool :=
  go code.toList 0 false
where
  go : List Char → Nat → Bool → Bool
    | [], _, _ => false
    | '\\' :: _ :: cs, d, true => go cs d true
    | '"' :: cs, d, str => go cs d !str
    | _ :: cs, d, true => go cs d true
    | '(' :: cs, d, false => go cs (d + 1) false
    | ')' :: cs, d, false => if d == 1 then cs.isEmpty else go cs (d - 1) false
    | _ :: cs, d, false => d != 0 && go cs d false

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
  | .stringOrder le, [a, b] =>
    s!"({leanName names "JSString"}.{if le then "le" else "lt"} {argument a} {argument b})"
  | .stringAppend left right, [a, b] =>
    -- The printer writes a string as an atom, an application or code in
    -- parentheses, and an application binds tighter than `++`, so a string
    -- operand needs no parentheses of its own.
    let part (p : StringPart) (x : String) : String := match p with
      | .string => x
      | .bigint => s!"({leanName names "JSString"}.ofInt {argument x})"
      | .boolean => s!"({leanName names "JSString"}.ofBool {argument x})"
    s!"({part left a} ++ {part right b})"
  | .stringLength, [a] =>
    s!"({js}.ofSafeInt (N := {names.typeParam}) (({leanName names "JSString"}.length {argument a} : " ++
      s!"{leanName names "Nat"}) : {leanName names "Int"}))"
  | .stringMethod .indexOf, args =>
    s!"({js}.ofSafeInt (N := {names.typeParam}) ({leanName names "JSString"}.indexOf " ++
      s!"{" ".intercalate (args.map argument)}))"
  | .stringMethod method, args =>
    s!"({leanName names "JSString"}.{method.name} {" ".intercalate (args.map argument)})"
  | .stringCodePoints, [s] => s!"({leanName names "JSString"}.codePoints {argument s})"
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
  | .setElems, [s] => s!"({leanName names "JSSet"}.elems {argument s})"
  | .mapEntries, [m] => s!"({leanName names "JSMap"}.entries {argument m})"
  | .mapOfList, [xs] => s!"({leanName names "JSMap"}.ofList {argument xs})"
  | .setOfList, [xs] => s!"({leanName names "JSSet"}.ofList {argument xs})"
  | .append, [a] => a
  | .append, lists =>
    s!"({" ++ ".intercalate (lists.map fun a => if wholeParens a then a else argument a)})"
  | .recordGet key keys, [r, k] =>
    let case (f : String) := s!"{(names.ref key).1}.{memberName f}"
    -- A key that is one constructor, as `r['a']` gives, reads its field.
    match keys.find? (case · == k) with
    | some f => s!"{argument r}.{f}"
    | Option.none =>
      s!"(match {k} with{String.join (keys.map fun f => s!" | {case f} => {argument r}.{f}")})"
  | .includes, [xs, x] => s!"{argument x} ∈ {argument xs}"
  | .includesNumber, [xs, x] =>
    s!"({leanName names "List.any"} {argument xs} ({js}.sameValueZero {argument x}))"
  | .length, [xs] =>
    let int := leanName names "Int"
    s!"({js}.ofSafeInt (N := {names.typeParam}) (({leanName names "List.length"} {argument xs} : {leanName names "Nat"}) : {int}))"
  | .indexLit k, [xs] => s!"{argument xs}[{k}]?"
  | .indexNumber, [xs, i] => s!"({js}.elementAt? {argument xs} {argument i})"
  | .countUp k, [b] => s!"({js}.countUp ({k} : {leanName names "Int"}) {argument b})"
  | .at k, [xs] =>
    if 0 ≤ k then s!"{argument xs}[{k.toNat}]?"
    else s!"({leanName names "List.reverse"} {argument xs})[{(-k - 1).toNat}]?"
  | .slice start stop, [xs] =>
    -- Each step takes its list as an argument already, and leaves out a drop
    -- of nothing.
    let rev (x : String) := s!"({leanName names "List.reverse"} {x})"
    let take (n : Int) (x : String) := s!"({leanName names "List.take"} {n.toNat} {x})"
    let drop (n : Int) (x : String) := if n == 0 then x else s!"({leanName names "List.drop"} {n.toNat} {x})"
    let xs := argument xs
    -- A negative bound counts from the end, which is the start of the
    -- reversed list.
    match stop with
    | Option.none => if 0 ≤ start then drop start xs else rev (take (-start) (rev xs))
    | some e =>
      if 0 ≤ start && 0 ≤ e then drop start (take e xs)
      else if 0 ≤ start then drop start (rev (drop (-e) (rev xs)))
      else if e < 0 then rev (drop (-e) (take (-start) (rev xs)))
      else ""
  | .pure, [a] => s!"({tolean.IR.wrapped (leanName names "pure") a})"
  | .error, [m] => s!"({tolean.IR.wrapped (leanName names "JSError.mk") m})"
  | _, _ => ""

instance : tolean.IR.PrintOp ExprExt := ⟨ExprExt.print⟩

/-- The operation names the string type, so the output imports its model.
An operation on strings may stand where no string type or literal is in
sight, such as `a.key < b.key` on an interface of another file. -/
def ExprExt.usesString : ExprExt → Bool
  | .stringOrder _ | .stringAppend .. | .stringLength | .stringMethod _ | .stringCodePoints => true
  | _ => false

end tolean.TypeScript.IR
