import tolean.TypeScript.IR
import tolean.TypeScript.Spec.Eval

/-!
The meaning of the Tolean IR with the TypeScript extension, as an evaluator
over the values of the interpreter in `Spec/Eval.lean`.

Each constructor of `IR.Expr` and `IR.Body` is one form of Lean code.
The evaluator gives it the value that the printed Lean computes, written as a
JavaScript value: an `Int` is `Val.int`, `none` is `Val.null`, `some v` is the
value of `v`, a list is `Val.list`, and a structure is `Val.obj` with its
fields in the declared order. A `let` adds a binding in front, as Lean's
shadowing does, and `let (x, y) := …` gives `x` and `y` their new values. An
operation that TypeScript adds, such as `JSNumber.add`, gets the values of its
arguments, and `ExprExt.apply` gives its value.

`translate_sound` in `Proof/Module.lean` proves one direction for every
program that the translator accepts: when this evaluator gives a value for a
call, the interpreter gives the same value. So this file is trusted to mean
what the printed Lean means, and to give a value where the printed Lean does.
A certificate checks that for its file (`Proof/Link.lean`), so a certified
file does not trust this evaluator.
-/
namespace tolean.TypeScript.IR

open tolean.TypeScript.Eval (Val Env Outcome)

variable {N : Type} [JSNumber N]

/-- The functions of the output of `file`, by name: their parameters and their
body. -/
def functions (decls : List Decl) : List (String × List String × Body) :=
  decls.filterMap fun
    | .function name params _ body => some (name, params.map (·.1), body)
    | .struct .. | .alias .. | .enum .. | .tagged .. | .errors .. => none

/-- The functions of the output of a program, under the file of each: the
output of each file, with that file's path. -/
def functionsOf (program : List (String × List Decl)) : List (DeclRef × List String × Body) :=
  program.flatMap fun (file, decls) =>
    (functions decls).map fun (name, params, body) => (⟨file, name⟩, params, body)

/-- `=` on the values that the output compares: integers, booleans and
strings. -/
def eqVal : Val N → Val N → Option Bool
  | .int a, .int b => some (decide (a = b))
  | .bool a, .bool b => some (decide (a = b))
  | .str a, .str b => some (decide (a = b))
  | _, _ => none

def NumberOp.apply : NumberOp → N → N → Val N
  | .add, a, b => .num (JSNumber.add a b)
  | .sub, a, b => .num (JSNumber.sub a b)
  | .mul, a, b => .num (JSNumber.mul a b)
  | .div, a, b => .num (JSNumber.div a b)
  | .bitAnd, a, b => .num (JSNumber.bitAnd a b)
  | .bitOr, a, b => .num (JSNumber.bitOr a b)
  | .bitXor, a, b => .num (JSNumber.bitXor a b)
  | .shiftLeft, a, b => .num (JSNumber.shiftLeft a b)
  | .shiftRight, a, b => .num (JSNumber.shiftRight a b)
  | .unsignedShiftRight, a, b => .num (JSNumber.unsignedShiftRight a b)
  | .lt, a, b => .bool (JSNumber.lt a b)
  | .le, a, b => .bool (JSNumber.le a b)
  | .eq, a, b => .bool (JSNumber.eq a b)

def NumberConstant.value : NumberConstant → N
  | .nan => JSNumber.nan | .posInf => JSNumber.posInf | .negInf => JSNumber.negInf

def NumberTest.apply : NumberTest → N → Bool
  | .isSafeInteger, a => (JSNumber.toSafeInt a).isSome
  | .isNaN, a => JSNumber.isNaN a
  | .isFinite, a => JSNumber.isFinite a
  | .isInteger, a => JSNumber.isInteger a

def NumberFn.apply : NumberFn → N → N
  | .floor => JSNumber.floor | .ceil => JSNumber.ceil | .trunc => JSNumber.trunc
  | .round => JSNumber.round | .abs => JSNumber.abs | .bitNot => JSNumber.bitNot

def BigintOp.apply : BigintOp → Int → Int → Int
  | .bitAnd => JSBigInt.bitAnd | .bitOr => JSBigInt.bitOr | .bitXor => JSBigInt.bitXor
  | .shiftLeft => JSBigInt.shiftLeft | .shiftRight => JSBigInt.shiftRight

/-- The string that ToString gives for one operand of `a + b` on strings. -/
def StringPart.toStr : StringPart → Val N → Option JSString
  | .string, .str s => some s
  | .bigint, .int i => some (JSString.ofInt i)
  | .boolean, .bool b => some (JSString.ofBool b)
  | _, _ => none

/-- A method of a string, on the string and the values of its arguments. -/
def StringMethod.apply : StringMethod → JSString → List (Val N) → Option (Val N)
  | .startsWith, s, args => Eval.oneString (fun p => .bool (s.startsWith p)) args
  | .endsWith, s, args => Eval.oneString (fun p => .bool (s.endsWith p)) args
  | .includes, s, args => Eval.oneString (fun p => .bool (s.includes p)) args
  | .indexOf, s, args => Eval.oneString (fun p => .num (JSNumber.ofSafeInt (s.indexOf p))) args
  | .trim, s, args => Eval.noArgs (.str s.trim) args
  | .trimStart, s, args => Eval.noArgs (.str s.trimStart) args
  | .trimEnd, s, args => Eval.noArgs (.str s.trimEnd) args
  | .split, s, args => Eval.oneString (fun sep => .list ((s.split sep).map .str)) args

/-- The elements of a list. -/
def listItems? : Val N → Option (List (Val N))
  | .list items => some items
  | _ => none

/-- An operation that TypeScript adds, on the values of its arguments. -/
def ExprExt.apply : ExprExt → List (Val N) → Option (Val N)
  | .number n, [] => some (.num (JSNumber.ofSafeInt n))
  | .numberConstant c, [] => some (.num c.value)
  | .numberNeg, [.num a] => some (.num (JSNumber.neg a))
  | .numberOp op, [.num a, .num b] => some (op.apply a b)
  | .numberNe, [.num a, .num b] => some (.bool !(JSNumber.eq a b))
  | .numberTest test, [.num a] => some (.bool (test.apply a))
  | .numberFn f, [.num a] => some (.num (f.apply a))
  | .dateOfNumber, [.num t] => some (.date (JSDate.timeClip t))
  | .dateMethod name, [.date t] => Eval.dateMethod name t []
  | .dateUtc, vs => (Eval.numbers? vs).map fun xs => .num (JSDate.utc xs)
  | .numberSameValue, [.num a, .num b] => some (.bool (JSNumber.sameValue a b))
  | .numberOfInt, [.int i] => some (.num (JSNumber.ofInt i))
  | .numberFold isMax, vs =>
    (Eval.numbers? vs).map fun xs => .num (if isMax then JSNumber.maximum xs else JSNumber.minimum xs)
  | .bigintOp op, [.int a, .int b] => some (.int (op.apply a b))
  | .bigintNot, [.int a] => some (.int (JSBigInt.bitNot a))
  | .bigintPow k, [.int a] => some (.int (a ^ k))
  | .stringOrder le, [.str a, .str b] => some (.bool (if le then a.le b else a.lt b))
  | .stringLength, [.str s] => some (.num (JSNumber.ofSafeInt s.length))
  | .stringMethod method, .str s :: args => method.apply s args
  | .stringAppend left right, [a, b] => do
    return .str ((← left.toStr a) ++ (← right.toStr b))
  | .undefined, [] => some .undefined
  -- `a === undefined` and `a !== undefined`, as `IsStrictlyEqual` gives them.
  | .isUndefined, [a] => some (.bool (a matches .undefined))
  | .isDefined, [a] => some (.bool !(a matches .undefined))
  -- `a?.f.g`, as the spec evaluates it.
  | .optField _ _, [.null] | .optField _ _, [.undefined] => some .undefined
  | .optField path _, [.obj fields] => Eval.getPath fields path
  -- `r[k]`, as the spec evaluates it: the property that the string `k` names.
  | .recordGet _ _, [.obj fields, .str k] => Eval.getKey fields k
  -- `x ∈ xs` and `List.any xs (JSNumber.sameValueZero x)`: whether an
  -- element is `x`, as `includes` compares them.
  | .includes, [.list xs, x] | .includesNumber, [.list xs, x] => (Eval.includesVal x xs).map .bool
  -- `xs.length`, `xs[k]?`, `JSNumber.elementAt? xs i` and `xs.at(k)`, as the
  -- spec reads them: `none` is `undefined`.
  | .length, [.list xs] => some (.num (JSNumber.ofSafeInt xs.length))
  | .indexLit k, [.list xs] => some (Eval.elementAt xs (some k))
  | .indexNumber, [.list xs, .num i] => some (Eval.elementAt xs (JSNumber.toSafeInt i))
  -- `JSNumber.countUp k b`: the values that the interpreter's counted loop
  -- visits. It has no value where `countUp?` gives none.
  | .countUp k, [.num b] => (JSNumber.countUp? k b).map fun xs => .list (xs.map .num)
  | .at k, [.list xs] => some (Eval.atVal xs k)
  | .slice start stop, [.list xs] => some (.list (Eval.sliceList xs start stop))
  -- The operations of a `Map`, as the spec gives them.
  | .mapEmpty, [] => some (.map [])
  | .mapGet, [.map entries, k] => (Eval.mapFind entries k).map (·.getD .undefined)
  | .mapHas, [.map entries, k] => (Eval.mapFind entries k).map (.bool ·.isSome)
  | .mapSize, [.map entries] => some (.num (JSNumber.ofSafeInt entries.length))
  | .mapSet, [.map entries, k, v] => (Eval.mapSet entries k v).map .map
  | .mapDelete, [.map entries, k] => (Eval.mapDelete entries k).map .map
  -- The operations of a `Set`, as the spec gives them.
  | .setEmpty, [] => some (.set [])
  | .setHas, [.set elems, x] => (Eval.setHas elems x).map .bool
  | .setSize, [.set elems] => some (.num (JSNumber.ofSafeInt elems.length))
  | .setAdd, [.set elems, x] => (Eval.setAdd elems x).map .set
  | .setDelete, [.set elems, x] => (Eval.setDelete elems x).map .set
  -- What a loop visits, as the spec's `iterValues` gives it: a JS entry is
  -- the array `[key, value]`, as a Lean pair is.
  | .setElems, [.set elems] => some (.list elems)
  | .mapEntries, [.map entries] => some (.list (entries.map fun (k, v) => .list [k, v]))
  | .mapOfList, [.list items] => (Eval.mapOfItems items).map .map
  | .setOfList, [.list items] => (Eval.setOfItems items).map .set
  -- The elements of an array literal with a spread, in order.
  | .append, lists => (lists.mapM listItems?).map fun items => .list items.flatten
  -- `pure a` is the value of `a`, as the result of a function that does not
  -- throw this time.
  | .pure, [a] => some a
  -- `JSError.mk m` is the object that `new Error(m)` makes.
  | .error, [.str m] => some (.error "Error" [("message", .str m)])
  -- `Thrown.«C» m a b` is the object that `new C(m, a, b)` makes: the
  -- message, then the fields.
  | .errorCase _ cls fields, .str m :: args =>
    if fields.length == args.length + 1 then
      some (.error cls ((fields.zip (.str m :: args)).filterMap fun (f, a) => f.map (·, a)))
    else none
  | _, _ => none

/-- The tag of `v`, a value of a tagged union: the string in its tag field
`field`, or the result of `typeof v` when the union has no tag field. -/
def tagOf : Option String → Val N → Option JSString
  | some field, .obj fields =>
    match fields.lookup field with
    | some (.str k) => some k
    | _ => none
  | some _, _ => none
  | none, v => some (JSString.ofString v.typeOf)

/-- The bindings that `let (x, y) := …` makes: each of `names`, with its value
in `inner`. A name that is bound already gets the new value in its place,
and a new name goes in front. So every lookup gives what Lean's shadowing
gives, and a loop leaves the environment the same length, which a
certificate's loop lemma needs. -/
def bindState (names : List String) (inner outer : Env N) : Option (Env N) :=
  names.foldlM (fun ρ n => do
    let v ← inner.lookup n
    return if (ρ.lookup n).isSome then Eval.Env.set ρ n v else (n, v) :: ρ) outer

mutual

/-- The value of `e`. `fuel` bounds the depth of nested calls. -/
def Expr.eval (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N) :
    Expr → Option (Val N)
  | .int n => some (.int n)
  | .none => some .null
  | .ascribe e _ => Expr.eval fs fuel ρ e
  | .bool b => some (.bool b)
  | .string s => some (.str (JSString.ofString s))
  | .var name => ρ.lookup name
  -- A constructor of a literal union is its string, as in JS.
  | .enumCase _ member => some (.str (JSString.ofString member))
  -- A tag field is its string in the object.
  | .tagValue value => some (.str (JSString.ofString value))
  -- A member of a tagged union is the value of the member: the object of
  -- its structure, or the primitive value itself.
  | .inject _ _ e => Expr.eval fs fuel ρ e
  -- A field that the object does not have is `undefined`, as in JS.
  | .field obj _ name => do
    match ← Expr.eval fs fuel ρ obj with
    | .obj fields => Eval.getProp fields name
    | _ => none
  | .propNot p | .not p => do
    let .bool b ← Expr.eval fs fuel ρ p | none
    return .bool !b
  | .neg a => do
    let .int i ← Expr.eval fs fuel ρ a | none
    return .int (-i)
  | .ite c a b => do
    let .bool t ← Expr.eval fs fuel ρ c | none
    if t then Expr.eval fs fuel ρ a else Expr.eval fs fuel ρ b
  -- A call that throws gives no value here. `Body.bind` runs a call that can
  -- throw.
  | .call ref args => do (← Expr.evalCall fs fuel ρ ref args).toOption
  | .list elems _ => do return .list (← Expr.evalList fs fuel ρ elems)
  -- A tuple is an array in JS, so its value is the list of its elements.
  | .tuple elems => do return .list (← Expr.evalList fs fuel ρ elems)
  | .proj e index _ => do
    let .list items ← Expr.eval fs fuel ρ e | none
    items[index]?
  | .struct fields _ _ => do return .obj (← Expr.evalFields fs fuel ρ fields)
  -- `{ base with f := e }` sets each field of the object `base` in its place,
  -- as the spread of `base` and then the properties do.
  | .structUpdate base fields => do
    let .obj obj ← Expr.eval fs fuel ρ base | none
    let us ← Expr.evalFields fs fuel ρ fields
    return .obj (us.foldl (fun acc (k, v) => Eval.setProp acc k v) obj)
  -- A value of `T | null` is never `undefined`. JS tells `undefined` from
  -- `null` with `===` but not with `==`, so the tests of `null` give no value
  -- for it.
  | .isNone a => do
    match ← Expr.eval fs fuel ρ a with
    | .null => return .bool true
    | .undefined => none
    | _ => return .bool false
  | .isSome a => do
    match ← Expr.eval fs fuel ρ a with
    | .null => return .bool false
    | .undefined => none
    | _ => return .bool true
  | .matchNull name whenNull whenValue => do
    match ← ρ.lookup name with
    | .null => Expr.eval fs fuel ρ whenNull
    | .undefined => none
    | _ => Expr.eval fs fuel ρ whenValue
  -- `none` is `null`, or `undefined` for an optional field, and `some v` is
  -- the value of `v`. So both forms take `a` unless it is `null` or
  -- `undefined`, as `??` does, and only then evaluate `b`.
  | .coalesce a b _ => do
    match ← Expr.eval fs fuel ρ a with
    | .null | .undefined => Expr.eval fs fuel ρ b
    | w => some w
  | .intOp op a b => do
    let .int x ← Expr.eval fs fuel ρ a | none
    let .int y ← Expr.eval fs fuel ρ b | none
    return .int (op.apply x y)
  | .order op a b => do
    let .int x ← Expr.eval fs fuel ρ a | none
    let .int y ← Expr.eval fs fuel ρ b | none
    return .bool (op.apply x y)
  | .division op a b => do
    let .int x ← Expr.eval fs fuel ρ a | none
    let .int y ← Expr.eval fs fuel ρ b | none
    return .int (op.apply x y)
  | .eq a b => do
    return .bool (← eqVal (← Expr.eval fs fuel ρ a) (← Expr.eval fs fuel ρ b))
  | .ne a b => do
    return .bool !(← eqVal (← Expr.eval fs fuel ρ a) (← Expr.eval fs fuel ρ b))
  | .propAnd p q | .and p q => do
    let .bool x ← Expr.eval fs fuel ρ p | none
    let .bool y ← Expr.eval fs fuel ρ q | none
    return .bool (x && y)
  | .propOr p q | .or p q => do
    let .bool x ← Expr.eval fs fuel ρ p | none
    let .bool y ← Expr.eval fs fuel ρ q | none
    return .bool (x || y)
  | .decide p => Expr.eval fs fuel ρ p
  | .push name a => do
    let .list xs ← ρ.lookup name | none
    return .list (xs ++ [← Expr.eval fs fuel ρ a])
  | .update op name a => do
    let .int x ← ρ.lookup name | none
    let .int y ← Expr.eval fs fuel ρ a | none
    return .int (op.apply x y)
  | .ext op args => do op.apply (← Expr.evalList fs fuel ρ args)
  -- `fun x => body` runs on each element in order, as the callback of the
  -- source's method does, and `List.any`, `List.all` and `List.find?` stop
  -- where it does. `List.find?` gives `none` when no element passes, which is
  -- `undefined`, as in JS.
  | .listMethod method items param _ body _ => do
    let .list xs ← Expr.eval fs fuel ρ items | none
    match method with
    | .map => return .list (← Expr.evalMap fs fuel ρ param body xs)
    | .filter => return .list (← Expr.evalFilter fs fuel ρ param body xs)
    | .any => return .bool (← Expr.evalFind fs fuel ρ param body true xs).isSome
    | .all => return .bool (← Expr.evalFind fs fuel ρ param body false xs).isNone
    | .find => return (← Expr.evalFind fs fuel ρ param body true xs).getD .undefined
    | .mapIdx index => return .list (← Expr.evalMapIdx fs fuel ρ param index body 0 xs)
    -- `findIndex` is the position of the first element that passes, as a
    -- number, or `-1`. `findLast` looks from the end.
    | .findIndex =>
      return .num (JSNumber.ofSafeInt (((← Expr.evalFindIdx fs fuel ρ param body 0 xs).map Int.ofNat).getD (-1)))
    | .findLast => return (← Expr.evalFind fs fuel ρ param body true xs.reverse).getD .undefined
    -- A sort calls the comparator on every pair of elements and gives the
    -- order of `Eval.sortValues`, as the interpreter does.
    | .sortWith other => return .list (← Eval.sortValues (Expr.evalCompare fs fuel ρ param other body) xs)
  -- `List.foldl` runs the function on each element in order, with the value
  -- so far bound to `acc`, as the callback of `reduce` does.
  | .listFold items init acc param _ body _ => do
    let .list xs ← Expr.eval fs fuel ρ items | none
    Expr.evalReduce fs fuel ρ acc param body (← Expr.eval fs fuel ρ init) xs
termination_by e => (fuel, sizeOf e, 0)

/-- A call of the function `ref` of the output with `args`: `.ok` of the
value it returns, or `.error` of the error it throws. -/
def Expr.evalCall (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N) (ref : DeclRef)
    (args : List Expr) : Option (Except (Val N) (Val N)) := do
  let vs ← Expr.evalList fs fuel ρ args
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let (params, body) ← fs.lookup ref
    if params.length != vs.length then none
    match ← Body.exec fs fuel (params.zip vs).reverse body with
    | .ret r => some r
    | .normal _ | .brk _ | .cont _ => none
termination_by (fuel, sizeOf args, 1)

/-- `List.map (fun param => body)` on `xs`. -/
def Expr.evalMap (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N)
    (param : String) (body : Expr) : List (Val N) → Option (List (Val N))
  | [] => some []
  | x :: xs => do
    return (← Expr.eval fs fuel ((param, x) :: ρ) body) :: (← Expr.evalMap fs fuel ρ param body xs)
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- The sign of the comparator `fun param other => body` on `x` and `y`, as
`Eval.evalCompare` reads it: `undefined` comes after every other value, and
the comparator must give a number. -/
def Expr.evalCompare (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N)
    (param other : String) (body : Expr) (x y : Val N) : Option Ordering :=
  match x, y with
  | .undefined, .undefined => some .eq
  | .undefined, _ => some .gt
  | _, .undefined => some .lt
  | _, _ => do
    let .num v ← Expr.eval fs fuel ((param, x) :: (other, y) :: ρ) body | none
    JSNumber.compareSign v
termination_by (fuel, sizeOf body, 1)

/-- `List.mapIdx (fun index param => body)` on `xs`, whose first element is at
position `start`. The body sees the position as a number. -/
def Expr.evalMapIdx (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N)
    (param index : String) (body : Expr) (start : Nat) : List (Val N) → Option (List (Val N))
  | [] => some []
  | x :: xs => do
    let v ← Expr.eval fs fuel ((param, x) :: (index, .num (JSNumber.ofSafeInt start)) :: ρ) body
    return v :: (← Expr.evalMapIdx fs fuel ρ param index body (start + 1) xs)
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- `List.foldl (fun acc param => body) v` on `xs`. -/
def Expr.evalReduce (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N)
    (acc param : String) (body : Expr) (v : Val N) : List (Val N) → Option (Val N)
  | [] => some v
  | x :: xs => do
    Expr.evalReduce fs fuel ρ acc param body (← Expr.eval fs fuel ((param, x) :: (acc, v) :: ρ) body) xs
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- `List.findIdx? (fun param => body)` on `xs`, whose first element is at
position `start`. -/
def Expr.evalFindIdx (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N)
    (param : String) (body : Expr) (start : Nat) : List (Val N) → Option (Option Nat)
  | [] => some none
  | x :: xs => do
    let .bool b ← Expr.eval fs fuel ((param, x) :: ρ) body | none
    if b then return some start
    Expr.evalFindIdx fs fuel ρ param body (start + 1) xs
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- `List.filter (fun param => body)` on `xs`, where `body` is a `Bool`. -/
def Expr.evalFilter (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N)
    (param : String) (body : Expr) : List (Val N) → Option (List (Val N))
  | [] => some []
  | x :: xs => do
    let .bool keep ← Expr.eval fs fuel ((param, x) :: ρ) body | none
    let rest ← Expr.evalFilter fs fuel ρ param body xs
    return if keep then x :: rest else rest
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- The first of `xs` for which the `Bool` `body` is `want`, or none. -/
def Expr.evalFind (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N)
    (param : String) (body : Expr) (want : Bool) : List (Val N) → Option (Option (Val N))
  | [] => some none
  | x :: xs => do
    let .bool b ← Expr.eval fs fuel ((param, x) :: ρ) body | none
    if b == want then return some x
    Expr.evalFind fs fuel ρ param body want xs
termination_by xs => (fuel, sizeOf body, xs.length + 1)

def Expr.evalList (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N) :
    List Expr → Option (List (Val N))
  | [] => some []
  | e :: es => do return (← Expr.eval fs fuel ρ e) :: (← Expr.evalList fs fuel ρ es)
termination_by es => (fuel, sizeOf es, 0)

def Expr.evalFields (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N) :
    List (String × Expr) → Option (List (String × Val N))
  | [] => some []
  | (key, e) :: rest => do
    return (key, ← Expr.eval fs fuel ρ e) :: (← Expr.evalFields fs fuel ρ rest)
termination_by fields => (fuel, sizeOf fields, 0)

/-- Run a body: it returns the function's value, or it ends in the state of a
branch or a loop body, with the bindings it has made. -/
def Body.exec (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N) :
    Body → Option (Outcome N)
  | .value e => do return .ret (.ok (← Expr.eval fs fuel ρ e))
  | .state _ | .yield .. => some (.normal ρ)
  | .done .. => some (.brk ρ)
  | .exit e _ => do return .ret (.ok (← Expr.eval fs fuel ρ e))
  | .throw e => do return .ret (.error (← Expr.eval fs fuel ρ e))
  -- `>>=` passes the error of the call on, and runs `rest` on its value.
  | .bind name ref args rest => do
    match ← Expr.evalCall fs fuel ρ ref args with
    | .ok v => Body.exec fs fuel ((name, v) :: ρ) rest
    | .error t => some (.ret (.error t))
  | .let name e rest => do Body.exec fs fuel ((name, ← Expr.eval fs fuel ρ e) :: ρ) rest
  -- A tuple is the list of its elements, and each name takes one, in order,
  -- as a `let` would.
  | .letTuple names e rest => do
    let .list vs ← Expr.eval fs fuel ρ e | none
    if names.length != vs.length then none
    Body.exec fs fuel ((names.zip vs).reverse ++ ρ) rest
  | .letArray name _ elems rest => do
    Body.exec fs fuel ((name, .list (← Expr.evalList fs fuel ρ elems)) :: ρ) rest
  | .ite c whenTrue whenFalse => do
    let .bool t ← Expr.eval fs fuel ρ c | none
    if t then Body.exec fs fuel ρ whenTrue else Body.exec fs fuel ρ whenFalse
  -- A value of `T | null` is never `undefined`, and an optional value is
  -- never `null`. So each test gives no value for the other, as the tests of
  -- `null` in expressions do.
  | .matchNull name optional whenNull whenValue => do
    match ← ρ.lookup name with
    | .null => if optional then none else Body.exec fs fuel ρ whenNull
    | .undefined => if optional then Body.exec fs fuel ρ whenNull else none
    | _ => Body.exec fs fuel ρ whenValue
  -- The tag is a field of the object, or the type of the value, so the
  -- evaluator reads it, as JS does. The arm of the one member left runs only
  -- for its tag, as the printed `match` on its constructor does.
  | .matchTag name _ field tag other whenTag whenOther => do
    let k ← tagOf field (← ρ.lookup name)
    if k == JSString.ofString tag then Body.exec fs fuel ρ whenTag
    else if other.all (JSString.ofString · == k) then Body.exec fs fuel ρ whenOther else none
  -- A branch that throws ends the function, as `>>=` passes the error on.
  | .letState names branch rest => do
    match ← Body.exec fs fuel ρ branch with
    | .normal inner => Body.exec fs fuel (← bindState names inner ρ) rest
    | .ret v => some (.ret v)
    | .brk _ | .cont _ => none
  | .fold names element body items rest _ => do
    let .list vs ← Expr.eval fs fuel ρ items | none
    match ← Body.runFold fs fuel names element body ρ vs with
    | .normal ρ' => Body.exec fs fuel ρ' rest
    | .ret v => some (.ret v)
    | .brk _ | .cont _ => none
termination_by b => (fuel, sizeOf b, 0)

/-- `List.foldl` over `items` with the step `fun (names) element => body`: the
bindings of `names` after each element, on top of `ρ`. A `break` in the body
ends the loop with the bindings it has then, as `forIn` stops at a
`ForInStep.done`. A `return` in the body ends it with the value to return. -/
def Body.runFold (fs : List (DeclRef × List String × Body)) (fuel : Nat) (names : List String)
    (element : String) (body : Body) (ρ : Env N) : List (Val N) → Option (Outcome N)
  | [] => some (.normal ρ)
  | x :: xs => do
    match ← Body.exec fs fuel ((element, x) :: ρ) body with
    | .normal inner => Body.runFold fs fuel names element body (← bindState names inner ρ) xs
    | .brk inner => return .normal (← bindState names inner ρ)
    | .ret v => some (.ret v)
    | .cont _ => none
termination_by xs => (fuel, sizeOf body, xs.length + 1)

end

/-- Call the function `key` of the output with `args`: `.ok` of the value it
returns, or `.error` of the error it throws. -/
def callIn (fs : List (DeclRef × List String × Body)) (key : DeclRef) (args : List (Val N))
    (fuel : Nat := 64) : Option (Except (Val N) (Val N)) := do
  let (params, body) ← fs.lookup key
  if params.length != args.length then none
  match ← Body.exec fs fuel (params.zip args).reverse body with
  | Outcome.ret r => some r
  | Outcome.normal _ | Outcome.brk _ | Outcome.cont _ => none

/-- The value that the call of the function `key` of the output returns, or
none when it throws. -/
def runIn (fs : List (DeclRef × List String × Body)) (key : DeclRef) (args : List (Val N))
    (fuel : Nat := 64) : Option (Val N) :=
  (callIn fs key args fuel).bind Except.toOption

end tolean.TypeScript.IR
