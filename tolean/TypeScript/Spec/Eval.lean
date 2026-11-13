import tolean.TypeScript.Syntax.Ast
import tolean.TypeScript.Spec.BigInt
import tolean.TypeScript.Spec.Date
import tolean.TypeScript.Spec.Number
import tolean.TypeScript.Spec.String

/-!
The meaning of the translated TypeScript subset, as an interpreter in Lean.

`eval` runs a parsed program: it reads the syntax tree that the parser
returns, with no translation in between. A certificate (`tolean certify`)
proves, for each function of one file, that `eval` and the translated Lean
give the same result. Then that file's translation no longer needs to be
trusted: only this interpreter and the parser do.

This file is trusted. Each rule follows ECMA-262 for the values the subset
has, and names the operation it follows. A rule returns `none` when the
program would throw, or when it leaves the subset; a certificate then fails.

A `number` is a value of an abstract type `N` with the operations of
`JSNumber` (`Spec/Number.lean`), the same model that the translation uses. So
the interpreter assumes nothing about doubles, and a certificate holds for
every model, real doubles among them.
-/
namespace tolean.TypeScript.Eval

open tolean.TypeScript.Syntax

variable {N : Type} [JSNumber N]

/-- A span, written short in certificates. -/
abbrev sp (a b c d : Nat) : tolean.Span := ⟨⟨a, b⟩, ⟨c, d⟩⟩

/-- A JavaScript value of the subset. A string is a `JSString`, its UTF-16
code units (`Spec/String.lean`). An object is a list of fields, in the order
the program wrote them. -/
inductive Val (N : Type) where
  | int (i : Int)
  | num (n : N)
  | bool (b : Bool)
  | str (s : JSString)
  | null
  /-- `undefined`, the value of a property that an object does not have. -/
  | undefined
  | list (items : List (Val N))
  | obj (fields : List (String × Val N))
  /-- A `Map`: its entries, in the order that `set` first added each key
  (ECMA-262 §24.1). -/
  | map (entries : List (Val N × Val N))
  /-- A `Set`: its elements, in the order that `add` first added each one
  (ECMA-262 §24.2). -/
  | set (elems : List (Val N))
  /-- An error object: the name of the class that made it, such as
  `"Error"`, and its own properties. `new Error(m)` has one, `message`. -/
  | error (cls : String) (fields : List (String × Val N))
  /-- A `Date`: its time value, or `none` when it is invalid (`JSDate`). -/
  | date (time : Option Int)
deriving Inhabited

/-- `ToBoolean` (ECMA-262 §7.1.2), on the values of the subset. A number is
false when it is `+0`, `-0` or `NaN`, and `-0 === 0`. -/
def Val.truthy : Val N → Bool
  | .int i => i != 0
  | .num n => !(JSNumber.isNaN n || JSNumber.eq n (JSNumber.ofSafeInt 0))
  | .bool b => b
  | .str s => !s.isEmpty
  | .null | .undefined => false
  | .list _ | .obj _ | .map _ | .set _ | .error _ _ | .date _ => true

/-- The result of `typeof` (ECMA-262 §13.5.3.1) on the values of the
subset. `null` is `"object"`, and so are an array and an object, which are
not callable. -/
def Val.typeOf : Val N → String
  | .int _ => "bigint"
  | .num _ => "number"
  | .bool _ => "boolean"
  | .str _ => "string"
  | .undefined => "undefined"
  | .null | .list _ | .obj _ | .map _ | .set _ | .error _ _ | .date _ => "object"

/-- The variables in scope, innermost first. -/
abbrev Env (N : Type) := List (String × Val N)

/-- Change the innermost variable named `name`. -/
def Env.set (env : Env N) (name : String) (v : Val N) : Env N :=
  match env with
  | [] => []
  | (n, old) :: rest => if n == name then (n, v) :: rest else (n, old) :: Env.set rest name v

/-- The value of one digit in base `radix`, or none. -/
def digitIn (radix : Nat) (c : Char) : Option Nat :=
  let v := if c.isDigit then c.toNat - '0'.toNat
    else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
    else radix
  if v < radix then some v else none

/-- The value of digits in base `radix`, or none if one is not a digit. -/
def digitsIn (radix : Nat) (digits : List Char) : Option Nat :=
  if digits.isEmpty then none
  else digits.foldlM (fun n c => return n * radix + (← digitIn radix c)) 0

/-- The value of a bigint literal such as `12n`, `1_000n` or `0x1fn`: the
MV of its `DecimalBigIntegerLiteral` or `NonDecimalIntegerLiteral`, with
separators dropped (`BigInt` literal, ECMA-262 §12.9.3). -/
def bigintLiteral (text : String) : Option Int :=
  let chars := (text.toList.filter (· != '_')).dropLast
  let value := match chars with
    | '0' :: p :: digits =>
      if p == 'x' || p == 'X' then digitsIn 16 digits
      else if p == 'o' || p == 'O' then digitsIn 8 digits
      else if p == 'b' || p == 'B' then digitsIn 2 digits
      else digitsIn 10 chars
    | _ => digitsIn 10 chars
  value.map (Int.ofNat ·)

/-- The value of a number literal such as `12`, `1_000`, `0x1f` or `1e3`, when
it is a safe integer: the MV of its `NumericLiteral`, with separators dropped
(ECMA-262 §12.9.3). A safe integer is exactly a double, so the literal is that
number. A literal with a fraction, or above `2^53 - 1`, leaves the subset. -/
def numberLiteral (text : String) : Option Int := do
  let chars := text.toList.filter (· != '_')
  let value : Int ← match chars with
    | '0' :: p :: digits =>
      if p == 'x' || p == 'X' then Int.ofNat <$> digitsIn 16 digits
      else if p == 'o' || p == 'O' then Int.ofNat <$> digitsIn 8 digits
      else if p == 'b' || p == 'B' then Int.ofNat <$> digitsIn 2 digits
      else decimal chars
    | _ => decimal chars
  if -maxSafe ≤ value && value ≤ maxSafe then some value else none
where
  /-- A `DecimalLiteral`, `digits.digits e±digits`, when its value is an integer. -/
  decimal (chars : List Char) : Option Int := do
    let (mantissa, exponent) := chars.span fun c => c != 'e' && c != 'E'
    let exp : Int ← match exponent with
      | [] => some 0
      | _ :: '-' :: ds => (fun n => -(n : Int)) <$> digitsIn 10 ds
      | _ :: '+' :: ds | _ :: ds => (fun n => (n : Int)) <$> digitsIn 10 ds
    let (whole, fraction) := mantissa.span (· != '.')
    let fraction := fraction.drop 1
    let m ← digitsIn 10 (whole ++ fraction)
    let scale := exp - fraction.length
    if scale ≥ 0 then
      -- Above 2^53 the literal leaves the subset anyway, so a large exponent
      -- need not be computed.
      if scale > 20 then (if m == 0 then some 0 else none) else some (m * 10 ^ scale.toNat)
    else
      let k := (-scale).toNat
      -- A long fraction of zeros is still zero.
      if m == 0 then some 0
      else if k > 400 then none else if m % 10 ^ k == 0 then some (m / 10 ^ k : Nat) else none

/-- `IsStrictlyEqual` (ECMA-262 §7.2.15) on primitive values, and between
`null` and any value. Values of different types are not equal, so `null` is
never equal to an object. Two objects compare by identity, which the subset
does not model, so they leave it. -/
def strictEq : Val N → Val N → Option Bool
  | .int a, .int b => some (decide (a = b))
  | .num a, .num b => some (JSNumber.eq a b)
  | .bool a, .bool b => some (decide (a = b))
  | .str a, .str b => some (decide (a = b))
  | .null, .null => some true
  | .undefined, .undefined => some true
  | .undefined, .int _ | .undefined, .num _ | .undefined, .bool _ | .undefined, .str _
  | .undefined, .null | .undefined, .list _ | .undefined, .obj _ | .undefined, .map _
  | .undefined, .set _ | .undefined, .error _ _ | .undefined, .date _ => some false
  | .int _, .undefined | .num _, .undefined | .bool _, .undefined | .str _, .undefined
  | .null, .undefined | .list _, .undefined | .obj _, .undefined | .map _, .undefined
  | .set _, .undefined | .error _ _, .undefined | .date _, .undefined => some false
  | .null, .int _ | .null, .num _ | .null, .bool _ | .null, .str _ | .null, .list _
  | .null, .obj _ | .null, .map _ | .null, .set _ | .null, .error _ _ | .null, .date _ => some false
  | .int _, .null | .num _, .null | .bool _, .null | .str _, .null | .list _, .null
  | .obj _, .null | .map _, .null | .set _, .null | .error _ _, .null | .date _, .null => some false
  | _, _ => none

/-- `IsLooselyEqual` (ECMA-262 §7.2.14) when one operand is `null` or
`undefined`. Each is loosely equal to itself and to the other, and to no
other value, so against any other value the test is `IsStrictlyEqual`.
Between two other values `==` converts its operands, which the subset does
not model, so they leave it. -/
def looseEq : Val N → Val N → Option Bool
  | .null, .undefined | .undefined, .null | .undefined, .undefined => some true
  | .undefined, b => strictEq .undefined b
  | a, .undefined => strictEq a .undefined
  | .null, b => strictEq .null b
  | a, .null => strictEq a .null
  | _, _ => none

/-- The properties of `Object.prototype` (ECMA-262 §20.1.3, and `__proto__`
and the accessor methods of Annex B.2.2). An object of the subset is an
object literal, so a read of a property that it does not have finds one of
these, or else `undefined`. -/
def objectPrototypeNames : List String :=
  ["constructor", "hasOwnProperty", "isPrototypeOf", "propertyIsEnumerable", "toLocaleString",
   "toString", "valueOf", "__proto__", "__defineGetter__", "__defineSetter__", "__lookupGetter__",
   "__lookupSetter__"]

/-- `obj.name` on an object literal with `fields` (`OrdinaryGet`, ECMA-262
§10.1.8.1): the value of its own property, or `undefined` when it has none.
A property of `Object.prototype` leaves the subset. -/
def getProp (fields : List (String × Val N)) (name : String) : Option (Val N) :=
  match fields.lookup name with
  | some v => some v
  | none => if objectPrototypeNames.contains name then none else some .undefined

/-- `obj[key]` with a string key: the property whose name is `key`, as
`getProp` reads it. A property name is a Lean `String`, so `getKey` compares
its UTF-16 code units with the key's. A key that holds a lone surrogate
then names no property, as in JS, where decoding the key would turn the
surrogate into U+FFFD and read a property of that name. -/
def getKey (fields : List (String × Val N)) (key : JSString) : Option (Val N) :=
  match (fields.find? fun p => JSString.ofString p.1 == key).map (·.2) with
  | some v => some v
  | none => if objectPrototypeNames.any (fun n => JSString.ofString n == key) then none else some .undefined

/-- Set the property `key` of an object with the fields `fields` to `v`
(`CreateDataProperty` on an ordinary object, ECMA-262 §7.3.5 and §10.1.6.3):
in its place when the object has it, and at the end when it does not. -/
def setProp (fields : List (String × Val N)) (key : String) (v : Val N) : List (String × Val N) :=
  if fields.any (·.1 == key) then fields.map fun (k, w) => (k, if k == key then v else w)
  else fields ++ [(key, v)]

/-- The property at `path` of an object with the fields `fields`, where each
property before the last is an object. -/
def getPath (fields : List (String × Val N)) : List String → Option (Val N)
  | [] => none
  | [f] => getProp fields f
  | f :: rest => do
    match ← getProp fields f with
    | .obj inner => getPath inner rest
    | _ => none

/-- A binary operator on two values, when neither operand short-circuits.
Bigint `/` and `%` truncate toward zero and throw on a zero divisor
(`BigInt::divide`, `BigInt::remainder`). On numbers and on strings, `a > b`
is `b < a` and `a >= b` is `b <= a`, as `IsLessThan` evaluates them
(ECMA-262 §13.10.1). Strings compare by their code units (§7.2.13). When
one operand of `+` is a string, `+` converts the other with ToString and
joins the code units (ApplyStringOrNumericBinaryOperator, §13.15.3). The
subset converts strings, bigints, booleans and numbers. A number becomes
`JSNumber.toStr`, which the model leaves abstract: `SafeIntLaws.toStr` says
what it gives for a safe integer. `/` on numbers is Number::divide
(§6.1.6.1.5), and the subset has no `%` on numbers.

On bigints, `a ** b` throws a `RangeError` when `b` is negative
(BigInt::exponentiate, §6.1.6.2.3), and `&`, `|`, `^`, `<<` and `>>` are the
operations of `JSBigInt` (`Spec/BigInt.lean`). `>>>` throws a `TypeError` on
bigints, so it has no rule there. On numbers, the bitwise operators work on
ToInt32 and ToUint32 of their operands, as `JSNumber.bitAnd` and its
relatives do (`Spec/Number.lean`). -/
def binary : BinOp → Val N → Val N → Option (Val N)
  | .add, .int a, .int b => some (.int (a + b))
  | .add, .str a, .str b => some (.str (a ++ b))
  | .add, .str a, .int b => some (.str (a ++ JSString.ofInt b))
  | .add, .int a, .str b => some (.str (JSString.ofInt a ++ b))
  | .add, .str a, .bool b => some (.str (a ++ JSString.ofBool b))
  | .add, .bool a, .str b => some (.str (JSString.ofBool a ++ b))
  | .add, .str a, .num n => some (.str (a ++ JSNumber.toStr n))
  | .add, .num n, .str b => some (.str (JSNumber.toStr n ++ b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .div, .int a, .int b => if b == 0 then none else some (.int (a.tdiv b))
  | .mod, .int a, .int b => if b == 0 then none else some (.int (a.tmod b))
  | .exp, .int a, .int b => if b < 0 then none else some (.int (a ^ b.toNat))
  | .bitAnd, .int a, .int b => some (.int (JSBigInt.bitAnd a b))
  | .bitOr, .int a, .int b => some (.int (JSBigInt.bitOr a b))
  | .bitXor, .int a, .int b => some (.int (JSBigInt.bitXor a b))
  | .shl, .int a, .int b => some (.int (JSBigInt.shiftLeft a b))
  | .shr, .int a, .int b => some (.int (JSBigInt.shiftRight a b))
  | .lt, .int a, .int b => some (.bool (decide (a < b)))
  | .gt, .int a, .int b => some (.bool (decide (a > b)))
  | .le, .int a, .int b => some (.bool (decide (a ≤ b)))
  | .ge, .int a, .int b => some (.bool (decide (a ≥ b)))
  | .add, .num a, .num b => some (.num (JSNumber.add a b))
  | .sub, .num a, .num b => some (.num (JSNumber.sub a b))
  | .mul, .num a, .num b => some (.num (JSNumber.mul a b))
  | .div, .num a, .num b => some (.num (JSNumber.div a b))
  | .bitAnd, .num a, .num b => some (.num (JSNumber.bitAnd a b))
  | .bitOr, .num a, .num b => some (.num (JSNumber.bitOr a b))
  | .bitXor, .num a, .num b => some (.num (JSNumber.bitXor a b))
  | .shl, .num a, .num b => some (.num (JSNumber.shiftLeft a b))
  | .shr, .num a, .num b => some (.num (JSNumber.shiftRight a b))
  | .ushr, .num a, .num b => some (.num (JSNumber.unsignedShiftRight a b))
  | .lt, .num a, .num b => some (.bool (JSNumber.lt a b))
  | .gt, .num a, .num b => some (.bool (JSNumber.lt b a))
  | .le, .num a, .num b => some (.bool (JSNumber.le a b))
  | .ge, .num a, .num b => some (.bool (JSNumber.le b a))
  | .lt, .str a, .str b => some (.bool (a.lt b))
  | .gt, .str a, .str b => some (.bool (b.lt a))
  | .le, .str a, .str b => some (.bool (a.le b))
  | .ge, .str a, .str b => some (.bool (b.le a))
  | .strictEq, a, b => (strictEq a b).map .bool
  | .strictNe, a, b => (strictEq a b).map (.bool ∘ not)
  | .looseEq, a, b => (looseEq a b).map .bool
  | .looseNe, a, b => (looseEq a b).map (.bool ∘ not)
  | _, _, _ => none

/-- SameValueZero (ECMA-262 §7.2.11) on the values of the subset. Two numbers
are the same when they are `===` or both `NaN`, and `+0` is the same as `-0`.
Any other two values are the same when they are `===` (SameValueNonNumber,
§7.2.12), so two objects leave the subset, as they do for `===`. -/
def sameValueZero : Val N → Val N → Option Bool
  | .num a, .num b => some (JSNumber.sameValueZero a b)
  | a, b => strictEq a b

/-- SameValue (ECMA-262 §7.2.10), which `Object.is` gives: on two numbers,
`===` except that `NaN` is the same as `NaN` and `+0` is not the same as
`-0`, and on any other two values, SameValueNonNumber, as for
`sameValueZero`. -/
def sameValue : Val N → Val N → Option Bool
  | .num a, .num b => some (JSNumber.sameValue a b)
  | a, b => strictEq a b

/-- A method of a date with the time value `t` that takes no arguments, on
the values of its arguments (`JSDate.method?`). -/
def dateMethod (method : String) (t : Option Int) : List (Val N) → Option (Val N)
  | [] => (JSDate.method? method).map fun f => .num (f ⟨t⟩)
  | _ => none

/-- `Number(v)` (§21.1.1.1) on the value of its one argument: a bigint
becomes the Number value for it, and a number stays itself. ToNumber of a
string or a boolean is not modelled. -/
def numberOf : List (Val N) → Option (Val N)
  | [.int i] => some (.num (JSNumber.ofInt i))
  | [.num x] => some (.num x)
  | _ => none

/-- Whether an element of `items` is the same as `v` by SameValueZero. This
is the loop of `Array.prototype.includes` (ECMA-262 §23.1.3.16), which
compares the elements in order and stops at the first that is. -/
def includesVal (v : Val N) : List (Val N) → Option Bool
  | [] => some false
  | x :: xs => do if ← sameValueZero v x then return true else includesVal v xs

/-- A method of an array that takes no callback, on the elements of the
array and the values of the arguments: `includes` with one argument
(`Array.prototype.includes`, ECMA-262 §23.1.3.16). Its second argument, the
index to start at, leaves the subset, and so does every other method. -/
def arrayMethod (method : String) (items : List (Val N)) : List (Val N) → Option (Val N)
  | [v] => if method == "includes" then (includesVal v items).map .bool else none
  | _ => none

/-- The value `f p` of a method whose arguments are one string `p`. Other
arguments leave the subset. -/
def oneString (f : JSString → Val N) : List (Val N) → Option (Val N)
  | [.str p] => some (f p)
  | _ => none

/-- The value `v` of a method that takes no arguments here. -/
def noArgs (v : Val N) : List (Val N) → Option (Val N)
  | [] => some v
  | _ => none

/-- The integer of a number argument, as ToIntegerOrInfinity gives it
(ECMA-262 §7.1.5): the integer that a literal names, whatever the model of
numbers, as for `xs.at(k)`, or else a safe integer. `lit` is the integer
literal that the argument is, if it is one. Any other value leaves the subset. -/
def intArg : Option Int → Val N → Option Int
  | some k, _ => some k
  | none, .num n => JSNumber.toSafeInt n
  | none, _ => none

/-- The value of a method whose arguments are a string `p` and perhaps a
number: `f p` without the number, and `g p k` with it, where `k` is its
integer. -/
def stringAndInt (f : JSString → Val N) (g : JSString → Int → Val N) :
    List (Val N) → List (Option Int) → Option (Val N)
  | [.str p], _ => some (f p)
  | [.str p, v], [_, k] => (intArg k v).map (g p)
  | _, _ => none

/-- The value `g k` of a method whose argument is one number, with the
integer `k`. -/
def oneInt (g : Int → Val N) : List (Val N) → List (Option Int) → Option (Val N)
  | [v], [k] => (intArg k v).map g
  | _, _ => none

/-- `s.slice(start, end)` on the values of its arguments: a missing start is
`0`, and a missing end is the length (ECMA-262 §22.1.3.22). -/
def sliceArgs (s : JSString) : List (Val N) → List (Option Int) → Option (Val N)
  | [], _ => some (.str (s.slice 0 none))
  | [a], [ka] => do return .str (s.slice (← intArg ka a) none)
  | [a, b], [ka, kb] => do return .str (s.slice (← intArg ka a) (some (← intArg kb b)))
  | _, _ => none

/-- `padStart` or `padEnd` on the values of its arguments, where `g n fill` is
the padded string: a missing filler is `" "` (ECMA-262 §22.1.3.17.1). -/
def padArgs (g : Int → JSString → JSString) : List (Val N) → List (Option Int) → Option (Val N)
  | [v], [k] => (intArg k v).map fun n => .str (g n (JSString.ofString " "))
  | [v, .str fill], [k, _] => (intArg k v).map fun n => .str (g n fill)
  | _, _ => none

/-- `toUpperCase` or `toLowerCase` on `s`, where `r` is the result that the
ASCII rule gives. Any other string leaves the subset, because its result
follows the Unicode version of the engine (ECMA-262 §22.1.3.30). -/
def asciiCase (r s : JSString) (args : List (Val N)) : Option (Val N) :=
  if s.isAscii then noArgs (.str r) args else none

/-- `s.at(k)` as a value: the string of one code unit, or `undefined`. -/
def stringAt (s : JSString) (k : Int) : Val N :=
  match s.at? k with
  | some c => .str c
  | none => .undefined

/-- A method of the string `s` that takes no callback, on the values of its
arguments `args`, where `lits` holds the integer literal that each argument
is, if it is one:

- `startsWith`, `endsWith`, `includes` and `indexOf` (ECMA-262 §22.1.3.25,
  §22.1.3.7, §22.1.3.8 and §22.1.3.9), with a string and perhaps a position;
- `trim`, `trimStart` and `trimEnd` (§22.1.3.32 to §22.1.3.34);
- `split` (§22.1.3.23), with a string separator and perhaps a limit;
- `at` (§22.1.3.1) and `slice` (§22.1.3.22);
- `toUpperCase` and `toLowerCase` (§22.1.3.30 and §22.1.3.28) on ASCII
  strings;
- `padStart` and `padEnd` (§22.1.3.17 and §22.1.3.16), with a length and
  perhaps a string to fill with.

ToString converts a string argument, and the subset has it on strings only.
ToIntegerOrInfinity converts a number argument, and the subset has it on
integer literals and safe integers (`intArg`). Other arguments leave the
subset. -/
def stringMethod (method : String) (s : JSString) (args : List (Val N)) (lits : List (Option Int)) :
    Option (Val N) :=
  if method == "startsWith" then
    stringAndInt (fun p => .bool (s.startsWith p)) (fun p k => .bool (s.startsWithFrom p k)) args lits
  else if method == "endsWith" then
    stringAndInt (fun p => .bool (s.endsWith p)) (fun p k => .bool (s.endsWithAt p k)) args lits
  else if method == "includes" then
    stringAndInt (fun p => .bool (s.includes p)) (fun p k => .bool (s.includesFrom p k)) args lits
  else if method == "indexOf" then
    stringAndInt (fun p => .num (JSNumber.ofSafeInt (s.indexOf p)))
      (fun p k => .num (JSNumber.ofSafeInt (s.indexOfFrom p k))) args lits
  else if method == "trim" then noArgs (.str s.trim) args
  else if method == "trimStart" then noArgs (.str s.trimStart) args
  else if method == "trimEnd" then noArgs (.str s.trimEnd) args
  else if method == "split" then
    stringAndInt (fun sep => .list ((s.split sep).map .str))
      (fun sep k => .list ((s.splitLimit sep k).map .str)) args lits
  else if method == "at" then oneInt (stringAt s) args lits
  else if method == "slice" then sliceArgs s args lits
  else if method == "padStart" then padArgs s.padStart args lits
  else if method == "padEnd" then padArgs s.padEnd args lits
  else if method == "toUpperCase" then asciiCase s.toUpperAscii s args
  else if method == "toLowerCase" then asciiCase s.toLowerAscii s args
  else none

mutual
/-- `JSON.stringify` throws a `TypeError` on `v`, because it reaches a bigint
(SerializeJSONProperty, ECMA-262 §25.5.2.2, step 10). It reads the elements of
an array and the own properties of an object, but not the entries of a map or
a set, which have no own properties. -/
def Val.jsonThrows : Val N → Bool
  | .int _ => true
  | .list items => jsonThrowsList items
  | .obj fields | .error _ fields => jsonThrowsFields fields
  | _ => false

/-- `JSON.stringify` throws on an element of `items`. -/
def jsonThrowsList : List (Val N) → Bool
  | [] => false
  | x :: xs => x.jsonThrows || jsonThrowsList xs

/-- `JSON.stringify` throws on the value of a field of `fields`. -/
def jsonThrowsFields : List (String × Val N) → Bool
  | [] => false
  | (_, x) :: fs => x.jsonThrows || jsonThrowsFields fs
end

/-- The code units of `text`, which is ASCII. -/
private def ascii (text : String) : List UInt16 := text.toList.map fun c => c.toNat.toUInt16

/-- QuoteJSONString (ECMA-262 §25.5.2.3): `s` in double quotes, with `"`, `\`
and the control characters escaped, and each lone surrogate as `\uXXXX`. -/
private def jsonQuote (s : JSString) : List UInt16 :=
  let hex (n : Nat) : List UInt16 :=
    ascii ("\\u" ++ String.ofList ((Nat.toDigits 16 (n + 0x10000)).drop 1))
  let escape : List UInt16 → List UInt16
    | [u] =>
      if u = 0x08 then ascii "\\b" else if u = 0x09 then ascii "\\t"
      else if u = 0x0A then ascii "\\n" else if u = 0x0C then ascii "\\f"
      else if u = 0x0D then ascii "\\r" else if u = 0x22 then ascii "\\\""
      else if u = 0x5C then ascii "\\\\"
      else if u.toNat < 0x20 || (0xD800 ≤ u.toNat && u.toNat < 0xE000) then hex u.toNat
      else [u]
    | pair => pair
  ascii "\"" ++ (JSString.codePointUnits s.units).flatMap escape ++ ascii "\""

/-- The text that `JSON.stringify(v)` gives, for the interpreter. A finite
number is its ToString, and `NaN` and the infinities are `null`
(SerializeJSONProperty, ECMA-262 §25.5.2.2, step 9). -/
private partial def jsonTextImpl {N : Type} [JSNumber N] (v : Val N) : JSString :=
  ⟨go v⟩
where
  go : Val N → List UInt16
    | .null | .undefined => ascii "null"
    | .bool b => ascii (if b then "true" else "false")
    | .str s => jsonQuote s
    -- `Date.prototype.toJSON` gives `null` for an invalid date and the text of
    -- `toISOString` for a valid one, which the model does not have yet.
    | .date none => ascii "null"
    | .date (some _) => panic! "the interpreter cannot write a date as JSON yet"
    | .num n => if JSNumber.isNaN n || !JSNumber.isFinite n then ascii "null" else (JSNumber.toStr n).units
    | .int _ => panic! "JSON.stringify throws on a bigint"
    | .list items => ascii "[" ++ (ascii ",").intercalate (items.map go) ++ ascii "]"
    | .obj fields | .error _ fields =>
      let present := fields.filter fun (_, x) => !(x matches .undefined)
      ascii "{" ++
        (ascii ",").intercalate (present.map fun (k, x) => jsonQuote (JSString.ofString k) ++ ascii ":" ++ go x) ++
        ascii "}"
    | .map _ | .set _ => ascii "{}"

/-- The text of `JSON.stringify(v)` (ECMA-262 §25.5.2), where `v` is not
`undefined` and reaches no bigint. The spec defines it fully, but the model
does not: it is opaque, so a proof cannot depend on the text. A theorem then
holds for the real `JSON.stringify`, because the text is a function of the
value. The interpreter writes the text with `jsonTextImpl`, which the logic
never sees. -/
@[implemented_by jsonTextImpl]
opaque jsonText {N : Type} [JSNumber N] (v : Val N) : JSString

/-- `JSON.stringify(v)`, with no replacer and no indent (ECMA-262 §25.5.2.1):
`undefined` for `undefined`, no value where it throws on a bigint, and the
opaque text otherwise. -/
def jsonStringify (v : Val N) : Option (Val N) :=
  match v with
  | .undefined => some .undefined
  | v => if v.jsonThrows then none else some (.str (jsonText v))

/-- The element of the array `items` whose index is the safe integer `i`, or
`undefined` when `i` is none or no index of the array. -/
def elementAt (items : List (Val N)) : Option Int → Val N
  | some i => if 0 ≤ i then items[i.toNat]?.getD .undefined else .undefined
  | none => .undefined

/-- SameValueZero (ECMA-262 §7.2.11), which a `Map` uses to compare keys, on
the keys of the subset: numbers, bigints, booleans and strings. Two numbers
are the same when they are `===` or both `NaN`, so a map has at most one `NaN`
key, and `+0` is the same key as `-0`. On the other keys SameValueZero is
`IsStrictlyEqual`. A key of another type leaves the subset. -/
def sameKey : Val N → Val N → Option Bool
  | .num a, .num b => some (JSNumber.sameValueZero a b)
  | .int a, .int b => some (decide (a = b))
  | .bool a, .bool b => some (decide (a = b))
  | .str a, .str b => some (decide (a = b))
  | _, _ => none

/-- The key that a map or a set stores when it adds `k`: `+0` when `k` is
`-0`, and `k` otherwise (`Map.prototype.set` and `Set.prototype.add`, ECMA-262
§24.1.3.9 and §24.2.4.1). A loop over the keys therefore never sees `-0`.
A number is `+0` or `-0` exactly when it is `=== 0`. -/
def storedKey : Val N → Val N
  | .num a => .num (if JSNumber.eq a (JSNumber.ofSafeInt 0) then JSNumber.ofSafeInt 0 else a)
  | k => k

/-- The value of the key `k` in the entries of a map, or `none` when no entry
has the key (`Map.prototype.get`, ECMA-262 §24.1.3.6). -/
def mapFind : List (Val N × Val N) → Val N → Option (Option (Val N))
  | [], _ => some none
  | (k', v) :: rest, k => do if ← sameKey k' k then return some v else mapFind rest k

/-- The entries after `Map.prototype.set` (ECMA-262 §24.1.3.9): the entry of
`k` gets the value `v` in its place, or a new entry goes last when no entry
has the key. The entry keeps the key that it has, and a new entry stores
`storedKey k`. -/
def mapSet : List (Val N × Val N) → Val N → Val N → Option (List (Val N × Val N))
  | [], k, v => some [(storedKey k, v)]
  | (k', v') :: rest, k, v => do
    if ← sameKey k' k then return (k', v) :: rest else return (k', v') :: (← mapSet rest k v)

/-- The entries after `Map.prototype.delete` (ECMA-262 §24.1.3.3), which
removes the entry of `k`. The other entries keep their order. -/
def mapDelete : List (Val N × Val N) → Val N → Option (List (Val N × Val N))
  | [], _ => some []
  | (k', v') :: rest, k => do
    if ← sameKey k' k then return rest else return (k', v') :: (← mapDelete rest k)

/-- Whether a set with the elements `elems` has `x` (`Set.prototype.has`,
ECMA-262 §24.2.4.8). -/
def setHas : List (Val N) → Val N → Option Bool
  | [], _ => some false
  | y :: rest, x => do if ← sameKey y x then return true else setHas rest x

/-- The elements after `Set.prototype.add` (ECMA-262 §24.2.4.1): `storedKey x`
goes last when the set does not have `x`, and the set stays as it is when it
does. -/
def setAdd (elems : List (Val N)) (x : Val N) : Option (List (Val N)) := do
  if ← setHas elems x then return elems else return elems ++ [storedKey x]

/-- The elements after `Set.prototype.delete` (ECMA-262 §24.2.4.4), which
removes `x`. The other elements keep their order. -/
def setDelete : List (Val N) → Val N → Option (List (Val N))
  | [], _ => some []
  | y :: rest, x => do
    if ← sameKey y x then return rest else return y :: (← setDelete rest x)

/-- The values that `for … of` visits in `v`: the elements of an array, in
order (`CreateArrayIterator`, ECMA-262 §23.1.5.1), the elements of a set, in
the order of insertion (`CreateSetIterator`, §24.2.6.1), and the entries of a
map, in the same order, each as the array `[key, value]` (`CreateMapIterator`,
§24.1.5.1). The subset does not change a map or a set while a loop runs over
it, so the loop sees the values that it had when it started. A string visits
its code points, each as a string (`CreateStringIterator`, §22.1.5.1), so a
surrogate pair is one value. -/
def iterValues : Val N → Option (List (Val N))
  | .list items => some items
  | .set elems => some elems
  | .map entries => some (entries.map fun (k, v) => .list [k, v])
  | .str s => some (s.codePoints.map .str)
  | _ => none

/-- The entries of a map that `new Map(items)` makes: each item, an array
`[key, value]`, is set in order, as `Map.prototype.set` sets it. An item of
another shape leaves the subset. -/
def mapOfItems (items : List (Val N)) : Option (List (Val N × Val N)) :=
  items.foldlM (fun entries item =>
    match item with
    | .list [k, v] => mapSet entries k v
    | _ => none) []

/-- The elements of a set that `new Set(items)` makes: each item is added in
order, as `Set.prototype.add` adds it. -/
def setOfItems (items : List (Val N)) : Option (List (Val N)) := items.foldlM setAdd []

/-- What a statement list does: it runs to its end with the variables it
leaves, or it ends the function, or a `break` or a `continue` ends it with the
variables at that point. These are the completion records of ECMA-262
(§6.2.4) that the subset can make. -/
inductive Outcome (N : Type) where
  | normal (env : Env N)
  /-- The function ends: it returns `v` when `r` is `.ok v`, and it throws `v`
  when `r` is `.error v`. A return and a throw pass through every statement
  of the subset in the same way, because the subset has no `try`, so one
  outcome holds both. -/
  | ret (r : Except (Val N) (Val N))
  | brk (env : Env N)
  | cont (env : Env N)
deriving Inhabited

/-- The names that the places of an array pattern bind, from the values that
iterating the value gives (`IteratorBindingInitialization`, ECMA-262
§8.6.3): each place takes the next value, or `undefined` when none is left,
and a hole skips one. -/
def placeBindings : List (Option String) → List (Val N) → List (String × Val N)
  | [], _ => []
  | x :: xs, vs => (x.map (·, vs.headD .undefined)).toList ++ placeBindings xs vs.tail

/-- The names that an array pattern binds from the values `vs`, in order. The
rest takes a new array of the values that the places leave. -/
def patternBindings (p : ArrayPattern) (vs : List (Val N)) : List (String × Val N) :=
  placeBindings p.elems vs ++ (p.rest.map (·, .list (vs.drop p.elems.length))).toList

/-- The text of a number literal. -/
def numberText? : Expr → Option String
  | .number _ text => some text
  | _ => none

/-- The integer that a number literal names, or a number literal after `-`,
such as `-1`. A literal is that integer whatever the model of numbers, as it
is for `xs[0]`. -/
def intLiteral? : Expr → Option Int
  | .number _ text => numberLiteral text
  | .unary _ .neg (.number _ text) => (numberLiteral text).map (- ·)
  | _ => none

/-- The start of a counted loop: an integer literal, perhaps after `-`, as
its integer. `-0` is not one, because its value is `-0` and not `0`. -/
def countStart? : Expr → Option Int
  | .number _ text => numberLiteral text
  | .unary _ .neg (.number _ text) => (numberLiteral text).bind fun k => if k == 0 then none else some (-k)
  | _ => none

/-- `items.at(k)` (`Array.prototype.at`, ECMA-262 §23.1.3.1), where `k` is
the integer of the argument: a negative `k` counts from the end. An index
outside the array gives `undefined`. -/
def atVal (items : List (Val N)) (k : Int) : Val N :=
  elementAt items (some (if 0 ≤ k then k else items.length + k))

/-- A relative index into an array of `len` elements, as `slice` reads its
arguments: a negative `k` counts from the end, and the result is clamped to
`0` and `len`. -/
def relIndex (len : Nat) (k : Int) : Nat :=
  if k < 0 then (len + k).toNat else min k.toNat len

/-- `items.slice(start, stop)` (`Array.prototype.slice`, ECMA-262
§23.1.3.28), where `start` and `stop` are the integers of the arguments: the
elements from `start` up to `stop`, or to the end when `stop` is none. -/
def sliceList {α : Type} (items : List α) (start : Int) (stop : Option Int) : List α :=
  let k := relIndex items.length start
  let final := match stop with
    | some e => relIndex items.length e
    | none => items.length
  (items.drop k).take (final - k)

/-- The comparator `cmp` is consistent for `items` (ECMA-262 §23.1.3.30.1):
for every pair of elements it gives a sign, the sign for `(b, a)` is the
reverse of the sign for `(a, b)`, and "`a` does not come after `b`" is
transitive. These are the conditions that the spec lists, with the order
between `<` and `=` made explicit. They make "does not come after" a total
preorder, and then exactly one order of the elements is sorted and stable. -/
def consistentOn {α : Type} (cmp : α → α → Option Ordering) (items : List α) : Bool :=
  items.all fun a => items.all fun b =>
    (cmp a b).isSome && cmp b a == (cmp a b).map Ordering.swap &&
      items.all fun c => !(cmp a b != some .gt && cmp b c != some .gt) || cmp a c != some .gt

/-- The elements of `items` in the order that `Array.prototype.sort` gives
them with the comparator `cmp` (SortIndexedProperties, ECMA-262
§23.1.3.30.1). An element comes after another only when `cmp` says that it
is greater, so equal elements keep their order: the sort is stable, as the
spec has required since ES2019. The spec leaves the order to the engine when
the comparator is not consistent for the elements, so the subset gives none
there. -/
def sortValues {α : Type} (cmp : α → α → Option Ordering) (items : List α) : Option (List α) :=
  if consistentOn cmp items then some (items.mergeSort fun a b => cmp a b != some .gt) else none


/-! ### Calls that can throw inside larger expressions

JS evaluates the operands of an expression in order, and a call that throws
ends the statement at once (ECMA-262 §13.15.2 and §13.3.6.1, and the
completion records of §6.2.4). The model rewrites each statement so that such
a call stands on its own: `const r0' = f(x)` before the statement, which then
reads `r0'` in its place. Every operand that JS evaluates before the call
moves out the same way, so the rewritten statements run the same operations
in the same order as the source. A statement whose whole value is a call
keeps it, because the statement already passes what the call throws on.

The translator rewrites a function body with the same function before it
translates it, so the body it translates is the body the model runs. Which
calls move depends on which functions can throw, and the model decides that
from the module alone (`mayThrow`): a function whose body has a `throw`, or
calls a function of the module that can throw, can throw. A name that the
module does not declare as a function, such as an imported function, does
not count, so a call of it stays where it is. The translator then refuses
such a call inside a larger expression when the function can throw.

JS has no `'` in a name, so no hoisted name hides a name of the source. -/

/-- The name of the `k`-th value that a function body hoists: `r0'`, `r1'`, … -/
def hoistName (k : Nat) : String := s!"r{k}'"

mutual

/-- The names of the functions that `e` calls, anywhere in it. -/
def Expr.callNames : Expr → List String
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ => []
  | .array _ es => Expr.callNamesList es
  | .object _ ps => Property.callNamesList ps
  | .paren _ e | .member _ e _ | .optMember _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e
  | .spread _ e | .asConst _ e | .satisfies _ e _ => Expr.callNames e
  | .index _ a b | .binary _ _ a b | .assign _ _ a b => Expr.callNames a ++ Expr.callNames b
  | .call _ (.ident _ name) args => name :: Expr.callNamesList args
  | .call _ c args => Expr.callNames c ++ Expr.callNamesList args
  | .cond _ a b c => Expr.callNames a ++ Expr.callNames b ++ Expr.callNames c
  | .arrow _ _ _ body => Expr.callNames body
  | .new _ _ _ args => Expr.callNamesList args

def Expr.callNamesList : List Expr → List String
  | [] => []
  | e :: es => Expr.callNames e ++ Expr.callNamesList es

def Property.callNamesList : List Property → List String
  | [] => []
  | .shorthand .. :: ps => Property.callNamesList ps
  | .keyValue _ _ v :: ps | .spread _ v :: ps => Expr.callNames v ++ Property.callNamesList ps

end

mutual

/-- The names of the functions that `s` calls, anywhere in it. -/
def Stmt.callNames : Stmt → List String
  | .varDecl _ { init := some e, .. } | .destructure _ _ _ _ e | .exprStmt _ e | .returnStmt _ (some e)
  | .throwStmt _ e => Expr.callNames e
  | .varDecl _ { init := none, .. } | .returnStmt _ none | .breakStmt _ | .continueStmt _ | .empty _ => []
  | .ifStmt _ t a (some b) => Expr.callNames t ++ Stmt.callNames a ++ Stmt.callNames b
  | .ifStmt _ t a none => Expr.callNames t ++ Stmt.callNames a
  | .forOfStmt _ _ _ e body | .forOfPattern _ _ _ e body | .whileStmt _ e body => Expr.callNames e ++ Stmt.callNames body
  | .forStmt _ init test update body =>
    (init.bind (·.init)).elim [] Expr.callNames ++ test.elim [] Expr.callNames ++
      update.elim [] Expr.callNames ++ Stmt.callNames body
  | .block _ ss => Stmt.callNamesList ss
  | .switchStmt _ d cs => Expr.callNames d ++ Stmt.callNamesClauses cs

def Stmt.callNamesList : List Stmt → List String
  | [] => []
  | s :: ss => Stmt.callNames s ++ Stmt.callNamesList ss

def Stmt.callNamesClauses : List (Option Expr × List Stmt) → List String
  | [] => []
  | (t, ss) :: cs => t.elim [] Expr.callNames ++ Stmt.callNamesList ss ++ Stmt.callNamesClauses cs

end

mutual

/-- `s` holds a `throw` statement. -/
def Stmt.hasThrow : Stmt → Bool
  | .throwStmt .. => true
  | .ifStmt _ _ a (some b) => Stmt.hasThrow a || Stmt.hasThrow b
  | .ifStmt _ _ a none => Stmt.hasThrow a
  | .forOfStmt _ _ _ _ body | .forOfPattern _ _ _ _ body | .forStmt _ _ _ _ body | .whileStmt _ _ body =>
    Stmt.hasThrow body
  | .block _ ss => Stmt.hasThrowList ss
  | .switchStmt _ _ cs => Stmt.hasThrowClauses cs
  | .varDecl .. | .destructure .. | .exprStmt .. | .returnStmt .. | .breakStmt _ | .continueStmt _
  | .empty _ => false

def Stmt.hasThrowList : List Stmt → Bool
  | [] => false
  | s :: ss => Stmt.hasThrow s || Stmt.hasThrowList ss

def Stmt.hasThrowClauses : List (Option Expr × List Stmt) → Bool
  | [] => false
  | (_, ss) :: cs => Stmt.hasThrowList ss || Stmt.hasThrowClauses cs

end

/-- The body of the function `name` of `m`, if `m` declares one. -/
def functionBody (m : Module) (name : String) : Option Stmt :=
  m.decls.findSome? fun
    | .function _ _ n _ _ _ body => if n == name then some body else none
    | _ => none

/-- `name` is a function of `m` that can throw, as far as `fuel` calls deep:
its body has a `throw`, or calls a function of `m` that can throw. -/
def mayThrowIn (m : Module) : Nat → String → Bool
  | 0, _ => false
  | fuel + 1, name =>
    match functionBody m name with
    | none => false
    | some body => Stmt.hasThrow body || (Stmt.callNames body).any (mayThrowIn m fuel)

/-- `name`, called from `m`, is a function that can throw. A chain of calls
through the functions of `m` is at most as long as the module, so that many
steps decide it. -/
def mayThrow (m : Module) (name : String) : Bool := mayThrowIn m (m.decls.length + 1) name

/-- `e` is a name or a literal, which hoisting would only rename. -/
def Expr.isAtom : Expr → Bool
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ => true
  | _ => false

mutual

/-- `e` is a literal whose parts are all literals: it reads no local and runs
no call, so where it runs changes nothing that the model observes. Such an
operand stays in place, because its type comes from its position. -/
def Expr.isClosedLiteral : Expr → Bool
  | .number .. | .bigint .. | .string .. | .bool .. | .null _ => true
  | .array _ es => Expr.isClosedLiteralList es
  | .object _ ps => Property.isClosedLiteralList ps
  | _ => false

def Expr.isClosedLiteralList : List Expr → Bool
  | [] => true
  | e :: es => Expr.isClosedLiteral e && Expr.isClosedLiteralList es

def Property.isClosedLiteralList : List Property → Bool
  | [] => true
  | .keyValue _ _ v :: ps => Expr.isClosedLiteral v && Property.isClosedLiteralList ps
  | .shorthand .. :: _ | .spread .. :: _ => false

end

mutual

/-- `e` holds a call of a function that `thr` says can throw, in a place that
JS evaluates whenever it evaluates `e`. A call in a branch of `?:`, after
`&&`, `||` or `??`, or in an arrow function may not run, so it stays where
it is. -/
def Expr.hoists (thr : String → Bool) : Expr → Bool
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ | .arrow .. => false
  | .array _ es => Expr.hoistsList thr es
  | .object _ ps => Property.hoistsList thr ps
  | .paren _ e | .member _ e _ | .optMember _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e
  | .spread _ e | .asConst _ e | .satisfies _ e _ => Expr.hoists thr e
  | .index _ a b | .assign _ _ a b => Expr.hoists thr a || Expr.hoists thr b
  | .binary _ .and a _ | .binary _ .or a _ | .binary _ .coalesce a _ => Expr.hoists thr a
  | .binary _ _ a b => Expr.hoists thr a || Expr.hoists thr b
  | .call _ (.ident _ name) args => thr name || Expr.hoistsList thr args
  | .call _ c args => Expr.hoists thr c || Expr.hoistsList thr args
  | .cond _ t _ _ => Expr.hoists thr t
  | .new _ _ _ args => Expr.hoistsList thr args

def Expr.hoistsList (thr : String → Bool) : List Expr → Bool
  | [] => false
  | e :: es => Expr.hoists thr e || Expr.hoistsList thr es

def Property.hoistsList (thr : String → Bool) : List Property → Bool
  | [] => false
  | .shorthand .. :: ps => Property.hoistsList thr ps
  | .keyValue _ _ v :: ps | .spread _ v :: ps => Expr.hoists thr v || Property.hoistsList thr ps

end

/-- What hoisting has produced so far: the declarations to put before the
statement, in order, and the number of the next name. -/
structure Hoisted where
  decls : List Stmt
  next : Nat

/-- Bind `e` to a fresh name before the statement, and read the name in its
place. An atom stays as it is, and so does a literal whose parts are all
literals. -/
def Hoisted.bind (h : Hoisted) (e : Expr) : Expr × Hoisted :=
  if Expr.isAtom e || Expr.isClosedLiteral e then (e, h) else
    let name := hoistName h.next
    (.ident (Expr.span e) name,
      { decls := h.decls ++ [.varDecl (Expr.span e) { kind := .const, name, type := none, init := some e }],
        next := h.next + 1 })

/-- An operand that JS evaluates before a call that can throw, after its own
calls have moved out: it moves out whole, so that it still runs before them.
An arrow function stays, and a spread moves its value. -/
def Hoisted.bindOperand (h : Hoisted) : Expr → Expr × Hoisted
  | .arrow s p ps body => (.arrow s p ps body, h)
  | .spread s e => let (e', h) := h.bind e; (.spread s e', h)
  | e => h.bind e

mutual

/-- Hoist the calls out of `e` that `thr` says can throw: each moves to a
declaration before the statement, with every operand that JS evaluates
before it, and `e` reads the names in their place. -/
def Expr.hoist (thr : String → Bool) (h : Hoisted) : Expr → Expr × Hoisted
  | .call s (.ident sn name) args =>
    let (args', h) := Expr.hoistOperands thr h args
    if thr name then h.bind (.call s (.ident sn name) args') else (.call s (.ident sn name) args', h)
  | .call s (.member ms recv mname) args =>
    -- The receiver of a method is evaluated before the arguments.
    let (recv', h) := Expr.hoist thr h recv
    let (recv', h) := if Expr.hoistsList thr args then h.bindOperand recv' else (recv', h)
    let (args', h) := Expr.hoistOperands thr h args
    (.call s (.member ms recv' mname) args', h)
  | .call s c args =>
    let (c', h) := Expr.hoist thr h c
    let (args', h) := Expr.hoistOperands thr h args
    (.call s c' args', h)
  | .array s es => let (es', h) := Expr.hoistOperands thr h es; (.array s es', h)
  | .object s ps => let (ps', h) := Property.hoistOperands thr h ps; (.object s ps', h)
  | .paren s e => let (e', h) := Expr.hoist thr h e; (.paren s e', h)
  | .member s e n => let (e', h) := Expr.hoist thr h e; (.member s e' n, h)
  | .optMember s e n => let (e', h) := Expr.hoist thr h e; (.optMember s e' n, h)
  | .unary s op e => let (e', h) := Expr.hoist thr h e; (.unary s op e', h)
  | .spread s e => let (e', h) := Expr.hoist thr h e; (.spread s e', h)
  | .asConst s e => let (e', h) := Expr.hoist thr h e; (.asConst s e', h)
  | .satisfies s e t => let (e', h) := Expr.hoist thr h e; (.satisfies s e' t, h)
  | .index s a b =>
    let (a', h) := Expr.hoist thr h a
    let (a', h) := if Expr.hoists thr b then h.bindOperand a' else (a', h)
    let (b', h) := Expr.hoist thr h b
    (.index s a' b', h)
  | .binary s .and a b => let (a', h) := Expr.hoist thr h a; (.binary s .and a' b, h)
  | .binary s .or a b => let (a', h) := Expr.hoist thr h a; (.binary s .or a' b, h)
  | .binary s .coalesce a b => let (a', h) := Expr.hoist thr h a; (.binary s .coalesce a' b, h)
  | .binary s op a b =>
    let (a', h) := Expr.hoist thr h a
    let (a', h) := if Expr.hoists thr b then h.bindOperand a' else (a', h)
    let (b', h) := Expr.hoist thr h b
    (.binary s op a' b', h)
  | .assign s op target value => let (v', h) := Expr.hoist thr h value; (.assign s op target v', h)
  | .cond s t a b => let (t', h) := Expr.hoist thr h t; (.cond s t' a b, h)
  | .new s c ts args => let (args', h) := Expr.hoistOperands thr h args; (.new s c ts args', h)
  | e => (e, h)
termination_by structural e => e

/-- Hoist the calls out of operands that JS evaluates in order. An operand
before the last one that holds such a call moves out whole, after its own
calls, so that it still runs before them. -/
def Expr.hoistOperands (thr : String → Bool) (h : Hoisted) : List Expr → List Expr × Hoisted
  | [] => ([], h)
  | e :: es =>
    let (e', h) := Expr.hoist thr h e
    let (e', h) := if Expr.hoistsList thr es then h.bindOperand e' else (e', h)
    let (es', h) := Expr.hoistOperands thr h es
    (e' :: es', h)
termination_by structural es => es

/-- The values of the properties of an object literal, in order. -/
def Property.hoistOperands (thr : String → Bool) (h : Hoisted) : List Property → List Property × Hoisted
  | [] => ([], h)
  | p :: ps =>
    let later := Property.hoistsList thr ps
    let (p', h) := match p with
      | .shorthand s n => (Property.shorthand s n, h)
      | .keyValue s k v =>
        let (v', h) := Expr.hoist thr h v
        let (v', h) := if later then h.bindOperand v' else (v', h)
        (Property.keyValue s k v', h)
      | .spread s v =>
        let (v', h) := Expr.hoist thr h v
        let (v', h) := if later then h.bindOperand v' else (v', h)
        (Property.spread s v', h)
    let (ps', h) := Property.hoistOperands thr h ps
    (p' :: ps', h)
termination_by structural ps => ps

end

/-- Hoist the calls out of the value of a statement. A value that is itself
a call keeps it, after the calls in its arguments, because the statement
passes what the call throws on. -/
def Expr.hoistValue (thr : String → Bool) (h : Hoisted) : Expr → Expr × Hoisted
  | .call s (.ident sn name) args =>
    let (args', h) := Expr.hoistOperands thr h args
    (.call s (.ident sn name) args', h)
  | e => Expr.hoist thr h e

/-- The body of a loop or a branch, from the statements that replace its
one statement `s`. When hoisting adds declarations before it, a block holds
them, as the body of a loop does. -/
def asBody (s : Stmt) : List Stmt → Stmt
  | [s'] => s'
  | ss => .block (Stmt.span s) ss

mutual

/-- The statements of a body with the calls that can throw hoisted out of
their statements, numbering the fresh names from `k` on. -/
def Stmt.hoistList (thr : String → Bool) (k : Nat) : List Stmt → List Stmt × Nat
  | [] => ([], k)
  | s :: ss =>
    let (ds, k) := Stmt.hoistOne thr k s
    let (ss', k) := Stmt.hoistList thr k ss
    (ds ++ ss', k)
termination_by structural ss => ss

/-- One statement, as the statements that replace it: the hoisted
declarations, then the statement with the names in place of the calls. -/
def Stmt.hoistOne (thr : String → Bool) (k : Nat) : Stmt → List Stmt × Nat
  | .varDecl s ⟨kind, name, type, some e⟩ =>
    let (e', h) := Expr.hoistValue thr ⟨[], k⟩ e
    (h.decls ++ [.varDecl s ⟨kind, name, type, some e'⟩], h.next)
  | .destructure s kind p t e =>
    let (e', h) := Expr.hoistValue thr ⟨[], k⟩ e
    (h.decls ++ [.destructure s kind p t e'], h.next)
  | .returnStmt s (some e) =>
    let (e', h) := Expr.hoistValue thr ⟨[], k⟩ e
    (h.decls ++ [.returnStmt s (some e')], h.next)
  | .exprStmt s e =>
    let (e', h) := Expr.hoist thr ⟨[], k⟩ e
    (h.decls ++ [.exprStmt s e'], h.next)
  | .throwStmt s e =>
    let (e', h) := Expr.hoist thr ⟨[], k⟩ e
    (h.decls ++ [.throwStmt s e'], h.next)
  | .ifStmt s t a b =>
    let (t', h) := Expr.hoist thr ⟨[], k⟩ t
    let (as, k) := Stmt.hoistOne thr h.next a
    match b with
    | some b =>
      let (bs, k) := Stmt.hoistOne thr k b
      (h.decls ++ [.ifStmt s t' (asBody a as) (some (asBody b bs))], k)
    | none => (h.decls ++ [.ifStmt s t' (asBody a as) none], k)
  | .forOfStmt s kind x e body =>
    let (e', h) := Expr.hoist thr ⟨[], k⟩ e
    let (bs, k) := Stmt.hoistOne thr h.next body
    (h.decls ++ [.forOfStmt s kind x e' (asBody body bs)], k)
  | .forOfPattern s kind p e body =>
    let (e', h) := Expr.hoist thr ⟨[], k⟩ e
    let (bs, k) := Stmt.hoistOne thr h.next body
    (h.decls ++ [.forOfPattern s kind p e' (asBody body bs)], k)
  -- JS evaluates the test and the update of a counted loop before each run,
  -- so a call in them stays where it is.
  | .forStmt s init test update body =>
    let (bs, k) := Stmt.hoistOne thr k body
    ([.forStmt s init test update (asBody body bs)], k)
  | .whileStmt s t body =>
    let (bs, k) := Stmt.hoistOne thr k body
    ([.whileStmt s t (asBody body bs)], k)
  | .block s ss =>
    let (ss', k) := Stmt.hoistList thr k ss
    ([.block s ss'], k)
  | .switchStmt s d cs =>
    let (d', h) := Expr.hoist thr ⟨[], k⟩ d
    let (cs', k) := Stmt.hoistClauses thr h.next cs
    (h.decls ++ [.switchStmt s d' cs'], k)
  | s => ([s], k)
termination_by structural s => s

def Stmt.hoistClauses (thr : String → Bool) (k : Nat) :
    List (Option Expr × List Stmt) → List (Option Expr × List Stmt) × Nat
  | [] => ([], k)
  | (t, ss) :: cs =>
    let (ss', k) := Stmt.hoistList thr k ss
    let (cs', k) := Stmt.hoistClauses thr k cs
    ((t, ss') :: cs', k)
termination_by structural cs => cs

end

/-- A function body with the calls that can throw hoisted out of its
statements. The model runs this body, and the translator translates it. -/
def Stmt.hoisted (thr : String → Bool) : Stmt → Stmt
  | .block s ss => .block s (Stmt.hoistList thr 0 ss).1
  | s => s

/-- The functions of the declarations `ds`, by name, where `thr` says which
functions can throw: their parameters and their body, with the calls that
can throw hoisted out of its statements. -/
def functionsIn (thr : String → Bool) (ds : List Decl) : List (String × List String × Stmt) :=
  ds.filterMap fun
    | .function _ _ name _ params _ body => some (name, params.map (·.name), Stmt.hoisted thr body)
    | _ => none

/-- The functions of the module, by name. -/
def functions (m : Module) : List (String × List String × Stmt) := functionsIn (mayThrow m) m.decls

/-! ### Programs of several files

A program is a list of files, each with its path and its module. In the
subset a file declares only functions, types and string enums. The only code
it runs of its own makes the object of each enum, when the file loads and so
before any function of the program runs. So an import binds a name to a
function or an enum of another file and does nothing else (ECMA-262
§16.2.1.6, `InitializeEnvironment`). A call looks up the name in the file
that runs: first among its own functions, then among the names it imports. A
name that no variable binds is looked up the same way among the enums. -/

/-- A program: the path of each file, and its module. -/
abbrev Program := List (String × Module)

/-- Where code runs: a program, and the file whose code it is. -/
structure Scope where
  program : Program
  file : String

/-- `path` with `.` and `..` segments resolved, or none when `..` would leave
the root. -/
def normalizeSegments : List String → List String → Option (List String)
  | acc, [] => some acc
  | acc, "." :: rest => normalizeSegments acc rest
  | acc, ".." :: rest => if acc.isEmpty then none else normalizeSegments acc.dropLast rest
  | acc, s :: rest => if s.isEmpty then none else normalizeSegments (acc ++ [s]) rest

/-- The file that `import … from source` in `file` names: `source` relative to
the directory of `file`. The source must name the `.ts` file itself, as
Node's type stripping requires and a bundler accepts, so that the import
names the same file wherever the code runs. Node reads a source as a URL, so
a source with `%`, `?`, `#` or `\` names no file here: a percent escape, a
query, a fragment and a backslash mean something else there. So does a source
whose last segment is not the file's name, such as `"./b.ts/."`, which names
a directory there. Any other source names no file of the program. -/
def resolvePath (file source : String) : Option String := do
  if source.any fun c => c == '%' || c == '?' || c == '#' || c == '\\' then none
  let segments := source.splitOn "/"
  unless segments.head? == some "." || segments.head? == some ".." do none
  let raw ← segments.getLast?
  unless raw.endsWith ".ts" && raw != ".ts" do none
  let dir ← normalizeSegments [] (file.splitOn "/").dropLast
  let path ← normalizeSegments dir segments
  return "/".intercalate path

/-- An export list of `m`, `export { name }`, names `name` without `type`. -/
def listsExport (m : Module) (name : String) : Bool :=
  m.decls.any fun
    | .exports _ names none => names.any fun n => !n.typeOnly && n.name == name
    | _ => false

/-- `m` declares `name` as a function that it exports, with `export` before
it or in an export list. -/
def exportsFunction (m : Module) (name : String) : Bool :=
  m.decls.any fun
    | .function _ exported n _ _ _ _ => (exported || listsExport m name) && n == name
    | _ => false

/-- The function that a call of `name` runs, in the file of `s`: the file's
own function, or else the exported function of the file it imports `name`
from. -/
def resolve (s : Scope) (name : String) : Option DeclRef := do
  let m ← s.program.lookup s.file
  if (functions m).any (·.1 == name) then return ⟨s.file, name⟩
  let target ← m.decls.findSome? fun
    | .import _ names source =>
      if names.any fun n => !n.typeOnly && n.name == name then resolvePath s.file source else none
    | _ => none
  let tm ← s.program.lookup target
  if exportsFunction tm name then return ⟨target, name⟩ else none

/-- The string enums that `m` declares, or only the exported ones when
`exportedOnly`: each with its name, and the name and the string of each
member. -/
def enumsOf (m : Module) (exportedOnly : Bool) : List (String × List (String × String)) :=
  m.decls.filterMap fun
    | .enum _ exported name members =>
      if exported || !exportedOnly then some (name, members.map fun x => (x.name, x.value)) else none
    | _ => none

/-- What the declaration `d` of the file `file` binds the name `name` to, when
it is a string enum or an import of `name` without `type`: the members of the
enum, or none when an import names something that is not an exported string
enum. -/
def enumBinding (p : Program) (file name : String) : Decl → Option (Option (List (String × String)))
  | .enum _ _ n members => if n == name then some (some (members.map fun x => (x.name, x.value))) else none
  | .import _ names source =>
    if names.any fun n => !n.typeOnly && n.name == name then
      some (do
        let target ← resolvePath file source
        let tm ← p.lookup target
        (enumsOf tm true).lookup name)
    else none
  | _ => none

/-- The members of the enum that the name `name` reads in the file of `s`. A
module binds each name once (ECMA-262 §16.2.1.1), so in a program that loads
the first declaration that binds it is the only one: the file's own enum, or
an import, which binds the exported enum of the file it names. An import with
`type` binds no value. -/
def resolveEnum (s : Scope) (name : String) : Option (List (String × String)) := do
  let m ← s.program.lookup s.file
  let members ← m.decls.findSome? (enumBinding s.program s.file name)
  members

/-- The object of a string enum. TypeScript compiles `enum T { A = "a" }` to
code that makes an object and sets the property `A` of it to `"a"`, for each
member in order. A string member has no reverse mapping, so the object has
no other property. -/
def enumObject (members : List (String × String)) : Val N :=
  .obj (members.map fun (k, v) => (k, .str v))

/-- Every function of the program, under the file that declares it. -/
def functionsOf (p : Program) : List (DeclRef × List String × Stmt) :=
  p.flatMap fun (file, m) => (functions m).map fun (name, params, body) => (⟨file, name⟩, params, body)

/-- The environment of a call: each parameter bound to its argument
(`FunctionDeclarationInstantiation`, ECMA-262 §10.2.11). A parameter that
the call passes no argument for is `undefined`, as an optional parameter is
when a call leaves it out. JS ignores arguments beyond the parameters, but
TypeScript refuses them, and the model gives no value for such a call. -/
def bindArgs (params : List String) (vs : List (Val N)) : Option (Env N) :=
  if params.length < vs.length then none
  else some (params.zip (vs ++ List.replicate (params.length - vs.length) .undefined)).reverse

/-- The numbers among `vs`, when every value is a number. -/
def numbers? : List (Val N) → Option (List N)
  | [] => some []
  | .num x :: vs => (numbers? vs).map (x :: ·)
  | _ :: _ => none

/-- A function of `Math` that the subset has, on the values of its arguments:
`Math.floor`, `ceil`, `trunc`, `round` and `abs` on one number, and
`Math.min` and `Math.max` on any count of numbers (ECMA-262 §21.3.2). These
convert a value of another type with ToNumber, or throw on a bigint, so the
subset has them on numbers only. -/
def mathCall (f : String) (args : List (Val N)) : Option (Val N) :=
  if f == "min" then (numbers? args).map (.num ∘ JSNumber.minimum)
  else if f == "max" then (numbers? args).map (.num ∘ JSNumber.maximum)
  else
    match args with
    | [.num x] =>
      if f == "floor" then some (.num (JSNumber.floor x))
      else if f == "ceil" then some (.num (JSNumber.ceil x))
      else if f == "trunc" then some (.num (JSNumber.trunc x))
      else if f == "round" then some (.num (JSNumber.round x))
      else if f == "abs" then some (.num (JSNumber.abs x))
      else none
    | _ => none

-- With the array callbacks and the map and set methods both in `eval`, this
-- block takes a little more than the default 200000 heartbeats to elaborate,
-- most of it in the proofs that each recursive call is smaller.
set_option maxHeartbeats 400000 in
mutual

/-- The value of `e`. `fuel` bounds the depth of nested calls, so that the
interpreter is a total function. -/
def eval (m : Scope) (fuel : Nat) (env : Env N) : Expr → Option (Val N)
  -- `NaN` and `Infinity` are properties of the global object (ECMA-262
  -- §19.1), unless a variable of the program hides them. Any other name
  -- that no variable binds can be a string enum of the module, or one that
  -- it imports, which is a binding of the module. In JS such a binding would
  -- also hide a global of the same name, and this rule reads the global
  -- instead, so an enum named `NaN` makes it less defined than JS. The
  -- translator refuses such a name.
  | .ident _ name =>
    match env.lookup name with
    | some v => some v
    | none =>
      if name == "NaN" then some (.num JSNumber.nan)
      else if name == "Infinity" then some (.num JSNumber.posInf)
      else if name == "undefined" then some .undefined
      else (resolveEnum m name).map enumObject
  | .bigint _ text => (bigintLiteral text).map .int
  | .number _ text => (numberLiteral text).map (.num ∘ JSNumber.ofSafeInt)
  | .bool _ b => some (.bool b)
  | .string _ s => some (.str (JSString.ofString s))
  | .null _ => some .null
  | .paren _ inner => eval m fuel env inner
  -- Type stripping removes `as const` and `satisfies T`.
  | .asConst _ e | .satisfies _ e _ => eval m fuel env e
  | .array _ elems => (evalElems m fuel env elems).map .list
  -- `{ ...e, a: v }`: the properties of the object `e`, in its order
  -- (`CopyDataProperties`, ECMA-262 §7.3.26), then each later property, set in
  -- its place when the object has it. A spread of anything but an object
  -- leaves the subset.
  | .object _ (.spread _ e :: ps) => do
    let .obj fs ← eval m fuel env e | none
    let rest ← evalProps m fuel env ps
    return .obj (rest.foldl (fun acc (k, v) => setProp acc k v) fs)
  | .object _ props => (evalProps m fuel env props).map .obj
  -- A property read after a `?.` is a part of its optional chain, which is
  -- `undefined` as a whole where the `?.` meets `null` or `undefined`
  -- (ECMA-262 §13.3.9.1). So `a?.b.c` is `undefined` when `a` is `null`,
  -- but `(a?.b).c` reads `.c` of `undefined`, which throws.
  | .member _ obj name =>
    if obj.optSpine then do
      match ← evalChain m fuel env obj with
      | none => some .undefined
      | some (.obj fields) => getProp fields name
      | some _ => none
    else do
      match ← eval m fuel env obj with
      | .obj fields => getProp fields name
      -- `xs.length`, the number of elements of an array (ECMA-262 §10.4.2).
      -- An array of the subset has fewer than 2^53 elements, so its length
      -- is a safe integer.
      | .list items => if name == "length" then some (.num (JSNumber.ofSafeInt items.length)) else none
      -- `s.length`: the number of code units (ECMA-262 §22.1.4.1). The
      -- subset reads no other property of a string.
      | .str s => if name == "length" then some (.num (JSNumber.ofSafeInt s.length)) else none
      -- `m.size` (ECMA-262 §24.1.3.10): the number of entries. A map has
      -- fewer than 2^53 entries, so the number is a safe integer.
      | .map entries =>
        if name == "size" then some (.num (JSNumber.ofSafeInt entries.length)) else none
      -- `s.size` (ECMA-262 §24.2.4.14), the number of elements.
      | .set elems => if name == "size" then some (.num (JSNumber.ofSafeInt elems.length)) else none
      | _ => none
  -- `obj?.name` is `undefined` when `obj` is `null` or `undefined`
  -- (ECMA-262 §13.3.9.1).
  | .optMember _ obj name => do
    match ← eval m fuel env obj with
    | .null | .undefined => some .undefined
    | .obj fields => getProp fields name
    | _ => none
  -- `xs[i]` on an array, with a number `i` (`OrdinaryGet` on an array exotic
  -- object, ECMA-262 §10.4.2): the element when `i` is an index of the
  -- array. Any other number is `undefined`, because no element and no
  -- property of `Array.prototype` has its string as a key. `-0` reads the
  -- element `0`, as its string is `"0"`. A number literal is the integer it
  -- names, whatever the model of numbers, so the rule reads that integer.
  --
  -- `obj[key]` with a string key (ECMA-262 §13.3.2.1): `ToPropertyKey` of a
  -- string is the string itself, so this reads the property as `obj.key`
  -- does. A key of another type leaves the subset.
  | .index _ obj key => do
    match ← eval m fuel env obj with
    | .list items =>
      match numberText? key with
      | some text => return elementAt items (some (← numberLiteral text))
      | none =>
        let .num n ← eval m fuel env key | none
        return elementAt items (JSNumber.toSafeInt n)
    | .obj fields =>
      let .str k ← eval m fuel env key | none
      getKey fields k
    | _ => none
  | .unary _ .not arg => do return .bool !(← eval m fuel env arg).truthy
  -- `typeof x` names the type of the value of `x` (ECMA-262 §13.5.3.1). On a
  -- name that is not bound, JS gives `"undefined"`, and the subset has no
  -- such value, so the rule gives none there, as for every unbound name.
  | .unary _ .typeof arg => do return .str (JSString.ofString (← eval m fuel env arg).typeOf)
  -- The source text `-Infinity` is `negInf`, the model's name for it. A
  -- variable named `Infinity` is negated as any other value is.
  | .unary _ .neg (.ident _ "Infinity") => do
    match env.lookup "Infinity" with
    | some (.int i) => some (.int (-i))
    | some (.num n) => some (.num (JSNumber.neg n))
    | some _ => none
    | none => some (.num JSNumber.negInf)
  | .unary _ .neg arg => do
    match ← eval m fuel env arg with
    | .int i => some (.int (-i))
    | .num n => some (.num (JSNumber.neg n))
    | _ => none
  -- `~a` on a bigint is `-a - 1` (BigInt::bitwiseNOT, §6.1.6.2.2), and on a
  -- number it is that of ToInt32 (Number::bitwiseNOT, §6.1.6.1.2).
  | .unary _ .bitNot arg => do
    match ← eval m fuel env arg with
    | .int i => some (.int (JSBigInt.bitNot i))
    | .num n => some (.num (JSNumber.bitNot n))
    | _ => none
  -- `&&`, `||` and `??` evaluate their right side only when they need it
  -- (ECMA-262 §13.13.1), and return an operand, not a boolean.
  | .binary _ .and l r => do
    let a ← eval m fuel env l
    if a.truthy then eval m fuel env r else some a
  | .binary _ .or l r => do
    let a ← eval m fuel env l
    if a.truthy then some a else eval m fuel env r
  | .binary _ .coalesce l r => do
    let a ← eval m fuel env l
    match a with
    | .null | .undefined => eval m fuel env r
    | _ => some a
  | .binary _ op l r => do binary op (← eval m fuel env l) (← eval m fuel env r)
  | .cond _ test t f => do
    if (← eval m fuel env test).truthy then eval m fuel env t else eval m fuel env f
  -- `Number.isNaN(x)`, `Number.isFinite(x)`, `Number.isSafeInteger(x)` and
  -- `Number.isInteger(x)` on a number (ECMA-262 §21.1.2), unless a variable
  -- hides `Number`.
  | .call _ (.member _ (.ident _ "Number") test) [arg] => do
    if (env.lookup "Number").isSome then none
    let .num n ← eval m fuel env arg | none
    if test == "isNaN" then some (.bool (JSNumber.isNaN n))
    else if test == "isFinite" then some (.bool (JSNumber.isFinite n))
    else if test == "isSafeInteger" then some (.bool (JSNumber.toSafeInt n).isSome)
    else if test == "isInteger" then some (.bool (JSNumber.isInteger n))
    else none
  -- `JSON.stringify(x)` (ECMA-262 §25.5.2.1), unless a variable hides `JSON`.
  -- The method and the arguments are checked in the body, as for `Math`, so
  -- that the rule adds few cases to the equations of `eval`.
  | .call _ (.member _ (.ident _ "JSON") f) args => do
    if (env.lookup "JSON").isSome || f != "stringify" then none
    let [arg] := args | none
    jsonStringify (← eval m fuel env arg)
  -- `Math.floor(x)` and the other functions of `Math` that `mathCall` has,
  -- unless a variable hides `Math`.
  | .call _ (.member _ (.ident _ "Math") f) args => do
    if (env.lookup "Math").isSome then none
    mathCall f (← evalList m fuel env args)
  -- `Date.UTC(year, month, …)` (§21.4.3.4) on numbers, unless a variable
  -- hides `Date`.
  | .call _ (.member _ (.ident _ "Date") "UTC") args => do
    if (env.lookup "Date").isSome then none
    return .num (JSDate.utc (← numbers? (← evalList m fuel env args)))
  -- `Object.is(a, b)` (§20.1.2.15), unless a variable hides `Object`.
  | .call _ (.member _ (.ident _ "Object") "is") [a, b] => do
    if (env.lookup "Object").isSome then none
    return .bool (← sameValue (← eval m fuel env a) (← eval m fuel env b))
  -- `xs.map(x => e)` and the other methods of an array that take a callback
  -- (`Array.prototype.map`, `filter`, `some`, `every` and `find`, ECMA-262
  -- §23.1.3.21, §23.1.3.8, §23.1.3.29, §23.1.3.6 and §23.1.3.9). The callback
  -- runs on each element in order, with `x` bound to it, until the method has
  -- its answer. It is an arrow function written at the call, so it sees the
  -- variables of the call, and nothing changes them while the method runs. The
  -- method also passes the index and the array, which an arrow with one
  -- parameter ignores.
  | .call _ (.member _ recv method) [.arrow _ _ [p] body] => do
    let .list items ← eval m fuel env recv | none
    if method == "map" then return .list (← evalMap m fuel env p.name body items)
    else if method == "filter" then return .list (← evalFilter m fuel env p.name body items)
    else if method == "some" then return .bool (← evalFind m fuel env p.name body true items).isSome
    else if method == "every" then
      return .bool (← evalFind m fuel env p.name body false items).isNone
    else if method == "find" then return (← evalFind m fuel env p.name body true items).getD .undefined
    -- `findIndex` (§23.1.3.10) gives the index of the element that `find`
    -- finds, or `-1`, and the index is a safe integer. `findLast`
    -- (§23.1.3.11) calls the callback on the elements from the last to the
    -- first.
    else if method == "findIndex" then
      return .num (JSNumber.ofSafeInt (((← evalFindIdx m fuel env p.name body 0 items).map Int.ofNat).getD (-1)))
    else if method == "findLast" then
      return (← evalFind m fuel env p.name body true items.reverse).getD .undefined
    else none
  -- `xs.at(k)` (`Array.prototype.at`, ECMA-262 §23.1.3.1). Its argument
  -- becomes an integer by `ToIntegerOrInfinity`. A literal is the integer it
  -- names, whatever the model of numbers. Any other number is its integer
  -- when it is a safe integer; truncating other numbers leaves the subset.
  -- `s.at(k)` on a string is a string method, as the last rule takes it.
  | .call _ (.member _ recv "at") [arg] => do
    match ← eval m fuel env recv with
    | .list items =>
      match intLiteral? arg with
      | some k => return atVal items k
      | none =>
        let .num n ← eval m fuel env arg | none
        return atVal items (← JSNumber.toSafeInt n)
    | .str s => stringMethod "at" s [← eval m fuel env arg] [intLiteral? arg]
    | _ => none
  -- `xs.slice(start, end)` (`Array.prototype.slice`, ECMA-262 §23.1.3.28).
  -- Each argument becomes an integer as the argument of `at` does. A missing
  -- start is `0`, and a missing end is the length. `s.slice` on a string is a
  -- string method.
  | .call _ (.member _ recv "slice") args => do
    match ← eval m fuel env recv with
    | .list items =>
      match args with
      | [] => return .list (sliceList items 0 none)
      | [a] => return .list (sliceList items (← evalInt m fuel env a) none)
      | [a, b] => return .list (sliceList items (← evalInt m fuel env a) (some (← evalInt m fuel env b)))
      | _ => none
    | .str s => stringMethod "slice" s (← evalList m fuel env args) (args.map intLiteral?)
    | _ => none
  -- `xs.map((x, i) => e)`: `map` passes the index too, as a number
  -- (ECMA-262 §23.1.3.21, step 6.c.ii). An array has fewer than 2^32
  -- elements, so the index is a safe integer. Two parameters of one arrow
  -- function may not have the same name (§15.3.1).
  --
  -- `xs.toSorted((a, b) => e)` (`Array.prototype.toSorted`, ECMA-262
  -- §23.1.3.34) gives a new array of the elements of `xs`, in the order that
  -- the comparator gives (`sortValues`). `sort` (§23.1.3.30) gives the same
  -- order, and it changes the array that it sorts. So the subset sorts only
  -- an array literal, such as `[...xs].sort((a, b) => e)`, which nothing else
  -- holds, and then the value is all that the call changes.
  | .call _ (.member _ recv method) [.arrow _ _ [p, q] body] => do
    if p.name == q.name then none
    if method == "map" then
      let .list items ← eval m fuel env recv | none
      return .list (← evalMapIdx m fuel env p.name q.name body 0 items)
    else if method == "toSorted" || (method == "sort" && recv.isArrayLiteral) then
      let .list items ← eval m fuel env recv | none
      return .list (← sortValues (evalCompare m fuel env p.name q.name body) items)
    else none
  -- `xs.reduce((acc, x) => e, init)` (`Array.prototype.reduce`, ECMA-262
  -- §23.1.3.24) with an initial value: the callback runs on each element in
  -- order, with `acc` bound to the value so far, which starts at `init`.
  -- `reduce` also passes the index and the array, which an arrow with two
  -- parameters ignores. Two parameters of one arrow function may not have the
  -- same name (§15.3.1).
  | .call _ (.member _ recv "reduce") [.arrow _ _ [a, p] body, init] => do
    if a.name == p.name then none
    let .list items ← eval m fuel env recv | none
    evalReduce m fuel env a.name p.name body (← eval m fuel env init) items
  -- `m.get(k)` and `m.has(k)` on a map (ECMA-262 §24.1.3.6 and §24.1.3.7).
  -- `get` gives `undefined` for a key that the map does not have.
  -- `s.has(x)` on a set (ECMA-262 §24.2.4.8).
  | .call _ (.member _ recv method) [arg] => do
    match ← eval m fuel env recv with
    | .map entries =>
      let found ← mapFind entries (← eval m fuel env arg)
      if method == "get" then return found.getD .undefined
      else if method == "has" then return .bool found.isSome
      else none
    | .set elems =>
      let found ← setHas elems (← eval m fuel env arg)
      if method == "has" then return .bool found else none
    -- An array or a string, as the next rule takes it.
    | .list items => arrayMethod method items [← eval m fuel env arg]
    | .str s => stringMethod method s [← eval m fuel env arg] [intLiteral? arg]
    | _ => none
  -- Any other call of a method of an array or a string, such as
  -- `xs.includes(v)` or `s.trim()`. The receiver comes first, then the
  -- arguments, as `EvaluateCall` takes them (ECMA-262 §13.3.6.2). Reading the
  -- method of an array or a string has no effect, so the rule reads it after
  -- the arguments.
  | .call _ (.member _ recv method) args => do
    match ← eval m fuel env recv with
    | .list items => arrayMethod method items (← evalList m fuel env args)
    | .str s => stringMethod method s (← evalList m fuel env args) (args.map intLiteral?)
    -- `d.getTime()` and the UTC getters of a date, which take no arguments.
    | .date t => dateMethod method t (← evalList m fuel env args)
    | _ => none
  -- A call that throws inside an expression gives no value. Only a call that
  -- is the whole value of a declaration or a `return` passes its throw on
  -- (`evalTop`).
  | .call _ (.ident _ name) args => do (← evalCall m fuel env name args).toOption
  -- `new Map()` (ECMA-262 §24.1.1.1): a map without entries, unless a
  -- variable hides the global `Map`. A declaration of the module named `Map`
  -- would hide it too, as one named `Number` would hide `Number`, and the
  -- translator refuses both.
  | .new _ "Map" _ [] => if (env.lookup "Map").isSome then none else some (.map [])
  -- `new Set()` (ECMA-262 §24.2.2.1), in the same way.
  | .new _ "Set" _ [] => if (env.lookup "Set").isSome then none else some (.set [])
  -- `new Date(t)` on a number (§21.4.2.1): the date whose time value is
  -- TimeClip of `t`.
  | .new _ "Date" _ [arg] => do
    if (env.lookup "Date").isSome then none
    let .num t ← eval m fuel env arg | none
    return .date (JSDate.timeClip t)
  -- `new Map(items)` and `new Set(items)` (`AddEntriesFromIterable`, ECMA-262
  -- §24.1.1.2, and §24.2.2.1): the constructor visits `items` as a loop
  -- would, and sets each `[key, value]`, or adds each value, in order.
  | .new _ "Map" _ [arg] => do
    if (env.lookup "Map").isSome then none
    return .map (← mapOfItems (← iterValues (← eval m fuel env arg)))
  | .new _ "Set" _ [arg] => do
    if (env.lookup "Set").isSome then none
    return .set (← setOfItems (← iterValues (← eval m fuel env arg)))
  -- `new Error(message)` with a string message (`Error`, ECMA-262
  -- §20.5.1.1): an error object whose own property `message` is the string,
  -- unless a variable hides `Error`. As for `NaN`, a function or an enum of
  -- the program named `Error` would hide the global in JS, and this rule
  -- reads the global; the translator refuses such a name.
  | .new _ "Error" [] [msg] => do
    if (env.lookup "Error").isSome then none
    let .str s ← eval m fuel env msg | none
    return .error "Error" [("message", .str s)]
  | _ => none
termination_by e => (fuel, sizeOf e, 0)

/-- A call of the function `name` of the program with `args`
(`EvaluateCall`, ECMA-262 §13.3.6.2): `.ok` of the value it returns, or
`.error` of the value it throws. -/
def evalCall (m : Scope) (fuel : Nat) (env : Env N) (name : String) (args : List Expr) :
    Option (Except (Val N) (Val N)) := do
  let vs ← evalList m fuel env args
  -- `Number(b)`, unless a variable hides `Number`. A declaration of the
  -- module named `Number` would hide it too, and the translator refuses it.
  if name == "Number" && (env.lookup "Number").isNone then return .ok (← numberOf vs)
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let key ← resolve m name
    let (params, body) ← (functionsOf m.program).lookup key
    -- The model holds a collection as a value, which is exact only when
    -- nothing else holds the object while the function changes it.
    if !Stmt.ownsChanges params body then none
    -- A `break` or a `continue` outside a loop is an early error
    -- (ECMA-262 §14.8.1 and §14.9.1), so the model gives no value.
    match ← execStmt { m with file := key.file } fuel (← bindArgs params vs) body with
    | .ret r => some r
    | .normal _ | .brk _ | .cont _ => none
termination_by (fuel, sizeOf args, 1)

/-- The value of `e` as the whole value of a declaration or a `return`: `.ok`
of its value, or `.error` of what it throws when it is a call that throws. -/
def evalTop (m : Scope) (fuel : Nat) (env : Env N) : Expr → Option (Except (Val N) (Val N))
  | .call _ (.ident _ name) args => evalCall m fuel env name args
  | e => (eval m fuel env e).map .ok
termination_by e => (fuel, sizeOf e, 1)

/-- An optional chain such as `a?.b.c`: `none` where a `?.` meets `null` or
`undefined`, which skips the rest of the chain, and the value of the chain
otherwise. -/
def evalChain (m : Scope) (fuel : Nat) (env : Env N) : Expr → Option (Option (Val N))
  | .optMember _ obj name => do
    match ← eval m fuel env obj with
    | .null | .undefined => some none
    | .obj fields => (getProp fields name).map some
    | _ => none
  | .member _ obj name => do
    match ← evalChain m fuel env obj with
    | none => some none
    | some (.obj fields) => (getProp fields name).map some
    | some _ => none
  | e => (eval m fuel env e).map some
termination_by e => (fuel, sizeOf e, 1)

/-- The integer of an argument such as the start of `slice`, by
`ToIntegerOrInfinity` (ECMA-262 §7.1.5): a literal is the integer it names,
whatever the model of numbers, and any other number is its integer when it
is a safe integer. Truncating any other number leaves the subset. -/
def evalInt (m : Scope) (fuel : Nat) (env : Env N) (e : Expr) : Option Int :=
  match intLiteral? e with
  | some k => some k
  | none => do
    let .num n ← eval m fuel env e | none
    JSNumber.toSafeInt n
termination_by (fuel, sizeOf e, 1)

def evalList (m : Scope) (fuel : Nat) (env : Env N) : List Expr → Option (List (Val N))
  | [] => some []
  | e :: es => do return (← eval m fuel env e) :: (← evalList m fuel env es)
termination_by es => (fuel, sizeOf es, 0)

/-- The values that an array literal holds (`ArrayAccumulation`, ECMA-262
§13.2.4.1): the value of each element, and in place of a spread `...e` each
value that iterating `e` gives, in order. The subset iterates an array, a set
and a map as `for … of` does (`iterValues`), and a spread of anything else
leaves the subset. -/
def evalElems (m : Scope) (fuel : Nat) (env : Env N) : List Expr → Option (List (Val N))
  | [] => some []
  | .spread _ e :: es => do
    return (← iterValues (← eval m fuel env e)) ++ (← evalElems m fuel env es)
  | e :: es => do return (← eval m fuel env e) :: (← evalElems m fuel env es)
termination_by es => (fuel, sizeOf es, 0)

def evalProps (m : Scope) (fuel : Nat) (env : Env N) :
    List Property → Option (List (String × Val N))
  | [] => some []
  -- `{ a }` evaluates the name `a`, so `{ NaN }` reads the global
  -- (`PropertyDefinitionEvaluation`, ECMA-262 §13.2.5.5).
  | .shorthand s name :: ps => do
    return (name, ← eval m fuel env (.ident s name)) :: (← evalProps m fuel env ps)
  -- `{ __proto__: v }` sets the prototype of the object instead of a key
  -- (ECMA-262 §13.2.5.5), and the model has no prototypes but
  -- `Object.prototype`.
  | .keyValue _ (.ident key) v :: ps => do
    if key == "__proto__" then none
    return (key, ← eval m fuel env v) :: (← evalProps m fuel env ps)
  | _ :: _ => none
termination_by ps => (fuel, sizeOf ps, 0)

/-- The callback `(name) => body` on each of `items`: the values that
`Array.prototype.map` puts in its new array. -/
def evalMap (m : Scope) (fuel : Nat) (env : Env N) (name : String) (body : Expr) :
    List (Val N) → Option (List (Val N))
  | [] => some []
  | x :: xs => do
    return (← eval m fuel ((name, x) :: env) body) :: (← evalMap m fuel env name body xs)
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- The callback `(name, index) => body` on each of `items`, where the first
of them is at position `start`: the values that `Array.prototype.map` puts
in its new array, when the callback reads the index. -/
def evalMapIdx (m : Scope) (fuel : Nat) (env : Env N) (name index : String) (body : Expr)
    (start : Nat) : List (Val N) → Option (List (Val N))
  | [] => some []
  | x :: xs => do
    let v ← eval m fuel ((name, x) :: (index, .num (JSNumber.ofSafeInt start)) :: env) body
    return v :: (← evalMapIdx m fuel env name index body (start + 1) xs)
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- The sign of the comparator `(a, b) => body` on the elements `x` and `y`
(CompareArrayElements, ECMA-262 §23.1.3.30.2). The sort puts `undefined`
after every other value without calling the comparator. The comparator must
give a number, whose sign `JSNumber.compareSign` reads. A bigint would throw
in `ToNumber`, and the spec reads any other value as a number, which the
subset does not, so both leave it. -/
def evalCompare (m : Scope) (fuel : Nat) (env : Env N) (a b : String) (body : Expr) (x y : Val N) :
    Option Ordering :=
  match x, y with
  | .undefined, .undefined => some .eq
  | .undefined, _ => some .gt
  | _, .undefined => some .lt
  | _, _ => do
    let .num v ← eval m fuel ((a, x) :: (b, y) :: env) body | none
    JSNumber.compareSign v
termination_by (fuel, sizeOf body, 1)

/-- The elements of `items` for which the callback `(name) => body` gives a
truthy value, in order: what `Array.prototype.filter` keeps. -/
def evalFilter (m : Scope) (fuel : Nat) (env : Env N) (name : String) (body : Expr) :
    List (Val N) → Option (List (Val N))
  | [] => some []
  | x :: xs => do
    let keep := (← eval m fuel ((name, x) :: env) body).truthy
    let rest ← evalFilter m fuel env name body xs
    return if keep then x :: rest else rest
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- The callback `(acc, name) => body` on each of `items` in order, where
`acc` is the value so far, which starts at `v`: the value of
`Array.prototype.reduce` with an initial value. -/
def evalReduce (m : Scope) (fuel : Nat) (env : Env N) (acc name : String) (body : Expr) (v : Val N) :
    List (Val N) → Option (Val N)
  | [] => some v
  | x :: xs => do evalReduce m fuel env acc name body (← eval m fuel ((name, x) :: (acc, v) :: env) body) xs
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- The position of the first of `items` for which `ToBoolean` of the
callback `(name) => body` is true, where the first of `items` is at
`start`, or none. The callback does not run on the elements after it. -/
def evalFindIdx (m : Scope) (fuel : Nat) (env : Env N) (name : String) (body : Expr) (start : Nat) :
    List (Val N) → Option (Option Nat)
  | [] => some none
  | x :: xs => do
    if (← eval m fuel ((name, x) :: env) body).truthy then return some start
    evalFindIdx m fuel env name body (start + 1) xs
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- The first of `items` for which `ToBoolean` of the callback
`(name) => body` is `want`, or none. The callback does not run on the
elements after it. `find` and `some` stop at the first truthy value, and
`every` at the first falsy one. -/
def evalFind (m : Scope) (fuel : Nat) (env : Env N) (name : String) (body : Expr) (want : Bool) :
    List (Val N) → Option (Option (Val N))
  | [] => some none
  | x :: xs => do
    if (← eval m fuel ((name, x) :: env) body).truthy == want then return some x
    evalFind m fuel env name body want xs
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- Run one statement. A block, and the branch of an `if`, keep the changes
they make to outer variables and drop the variables they declare. -/
def execStmt (m : Scope) (fuel : Nat) (env : Env N) : Stmt → Option (Outcome N)
  | .varDecl _ { name, init := some init, .. } => do
    match ← evalTop m fuel env init with
    | .ok v => return .normal ((name, v) :: env)
    | .error t => return .ret (.error t)
  -- `const [a, , b, ...r] = e` (ECMA-262 §14.3.3.1): the pattern iterates the
  -- value of `e`, as `for … of` does, and binds each name in order. A value
  -- that the subset cannot iterate leaves it.
  | .destructure _ _ p _ init => do
    match ← evalTop m fuel env init with
    | .ok v => return .normal ((patternBindings p (← iterValues v)).reverse ++ env)
    | .error t => return .ret (.error t)
  | .returnStmt _ (some e) => do return .ret (← evalTop m fuel env e)
  -- `throw e` ends the function with what it throws (ECMA-262 §14.14.1).
  | .throwStmt _ e => do return .ret (.error (← eval m fuel env e))
  -- `xs.push(v)` adds `v` at the end (`Array.prototype.push`, ECMA-262
  -- §23.1.3.23). The subset pushes only onto an array that the function owns,
  -- which nothing else can see, so the push changes only the variable.
  -- `evalCall` checks that the function owns it (`Stmt.ownsChanges`).
  | .exprStmt _ (.call _ (.member _ (.ident _ name) "push") [arg]) => do
    let .list items ← env.lookup name | none
    return .normal (env.set name (.list (items ++ [← eval m fuel env arg])))
  -- `m.set(k, v)` and `m.delete(k)` (ECMA-262 §24.1.3.9 and §24.1.3.3) on a
  -- map that the function owns, as for `push`: nothing else can see the
  -- map, so the change shows only in the variable. `evalCall` checks that
  -- the function owns the map, as for `push`.
  | .exprStmt _ (.call _ (.member _ (.ident _ name) "set") [key, value]) => do
    let .map entries ← env.lookup name | none
    let k ← eval m fuel env key
    let v ← eval m fuel env value
    return .normal (env.set name (.map (← mapSet entries k v)))
  -- `s.add(x)` and `s.delete(x)` on a set (ECMA-262 §24.2.4.1 and
  -- §24.2.4.4), in the same way.
  | .exprStmt _ (.call _ (.member _ (.ident _ name) "delete") [key]) => do
    match ← env.lookup name with
    | .map entries => return .normal (env.set name (.map (← mapDelete entries (← eval m fuel env key))))
    | .set elems => return .normal (env.set name (.set (← setDelete elems (← eval m fuel env key))))
    | _ => none
  | .exprStmt _ (.call _ (.member _ (.ident _ name) "add") [elem]) => do
    let .set elems ← env.lookup name | none
    return .normal (env.set name (.set (← setAdd elems (← eval m fuel env elem))))
  | .exprStmt _ (.assign _ .assign (.ident _ name) value) => do
    return .normal (env.set name (← eval m fuel env value))
  -- `x ??= e` (`LogicalAssignment`, ECMA-262 §13.15.2): `e` runs, and its
  -- value goes to `x`, only when `x` is `null` or `undefined`.
  | .exprStmt _ (.assign _ .coalesce (.ident _ name) value) => do
    match ← env.lookup name with
    | .null | .undefined => return .normal (env.set name (← eval m fuel env value))
    | _ => return .normal env
  | .exprStmt _ (.assign _ op (.ident _ name) value) => do
    let bop ← match op with
      | .add => some BinOp.add | .sub => some .sub | .mul => some .mul | _ => none
    return .normal (env.set name (← binary bop (← env.lookup name) (← eval m fuel env value)))
  | .ifStmt _ test t f => do
    let out ← if (← eval m fuel env test).truthy then execStmt m fuel env t
      else match f with
        | some f => execStmt m fuel env f
        | none => some (.normal env)
    match out with
    | .ret v => some (.ret v)
    | .normal env' => some (.normal (env'.drop (env'.length - env.length)))
    | .brk env' => some (.brk (env'.drop (env'.length - env.length)))
    | .cont env' => some (.cont (env'.drop (env'.length - env.length)))
  | .block _ body => do
    match ← exec m fuel env body with
    | .ret v => some (.ret v)
    | .normal env' => some (.normal (env'.drop (env'.length - env.length)))
    | .brk env' => some (.brk (env'.drop (env'.length - env.length)))
    | .cont env' => some (.cont (env'.drop (env'.length - env.length)))
  | .empty _ => some (.normal env)
  -- `break` and `continue` without a label (ECMA-262 §14.8.2 and §14.9.2).
  | .breakStmt _ => some (.brk env)
  | .continueStmt _ => some (.cont env)
  -- `for (const x of xs)` on an array, a set, a map or a string: the body runs once for
  -- each value that `iterValues` gives, in order, with `x` bound to it in a
  -- new scope (`ForIn/OfBodyEvaluation`, ECMA-262 §14.7.5.7).
  -- A JS loop sees a change to what it runs over while it runs: it visits an
  -- element that the body pushes or adds, and skips one that the body
  -- deletes before the loop reaches it. The model takes the values when the
  -- loop starts, so it gives no value for a body that changes them.
  | .forOfStmt _ .const name iterable body => do
    if Stmt.mutatesIterable iterable body then none
    execLoop m fuel env (fun v => some [(name, v)]) body (← iterValues (← eval m fuel env iterable))
  -- `for (const [k, v] of xs)`: each run binds the names of the pattern to
  -- the values that iterating the item gives, as `const [k, v] = item` does
  -- (`ForDeclarationBindingInitialization`, ECMA-262 §14.7.5.3).
  | .forOfPattern _ .const p iterable body => do
    if Stmt.mutatesIterable iterable body then none
    execLoop m fuel env (fun v => do return (patternBindings p (← iterValues v)).reverse) body
      (← iterValues (← eval m fuel env iterable))
  -- `for (let i = k; i < b; i++)` (`ForStatement`, ECMA-262 §14.7.4.2), where
  -- the start `k` is an integer literal: `execCounted` runs the body once for
  -- each value of `i`, in order, with `i` bound to it in a new scope, as in
  -- `CreatePerIterationEnvironment`. JS reads `b` before each run, and the
  -- model reads it once. `countedChanges` checks that the body changes
  -- nothing that `b` reads, so each read gives the same value.
  | .forStmt _ (some ⟨.let, name, _, some start⟩) (some (.binary _ .lt (.ident _ n) bound)) (some update)
      body => do
    if !(n == name && update.incrementsName name) then none
    if Stmt.countedChanges name bound body then none
    let k ← countStart? start
    let .num b ← eval m fuel env bound | none
    execCounted m fuel env name body b k (maxSafe - k + 1).toNat
  -- `switch (d) { … }` (`SwitchStatement` Evaluation, ECMA-262 §14.12.4): the
  -- clauses run in a new scope, and a `break` at the top of a clause ends the
  -- statement. The model leaves out a local declared at the top of a clause,
  -- which the whole case block shares.
  | .switchStmt _ disc clauses => do
    if clausesDeclare clauses then none
    let v ← eval m fuel env disc
    match ← execSwitch m fuel env v clauses with
    | .ret r => some (.ret r)
    | .normal env' => some (.normal (env'.drop (env'.length - env.length)))
    | .brk env' => some (.brk (env'.drop (env'.length - env.length)))
    | .cont env' => some (.cont (env'.drop (env'.length - env.length)))
  | _ => none
termination_by s => (fuel, sizeOf s, 0)

/-- `CaseBlockEvaluation` (ECMA-262 §14.12.4), for a case block whose
`default`, if it has one, is its last clause: the tests of the `case` clauses
run in order, and the first that is `===` to `v` selects its clause. That
clause and the ones after it run. When no test holds, the `default` clause
runs. The interpreter leaves a `default` before other clauses out of the
subset. -/
def execSwitch (m : Scope) (fuel : Nat) (env : Env N) (v : Val N) :
    List (Option Expr × List Stmt) → Option (Outcome N)
  | [] => some (.normal env)
  | [(none, body)] => execFrom m fuel env [(none, body)]
  | (none, _) :: _ :: _ => none
  | (some test, body) :: rest => do
    if ← strictEq v (← eval m fuel env test) then execFrom m fuel env ((some test, body) :: rest)
    else execSwitch m fuel env v rest
termination_by cs => (fuel, sizeOf cs, 1)

/-- Run the statements of `clauses`, from the selected one on: a clause that
does not end in `break` or `return` runs into the next. -/
def execFrom (m : Scope) (fuel : Nat) (env : Env N) :
    List (Option Expr × List Stmt) → Option (Outcome N)
  | [] => some (.normal env)
  | (_, body) :: rest => do
    match ← execCase m fuel env body with
    | (.ret r, _) => some (.ret r)
    | (.normal env', true) => some (.normal env')
    | (.normal env', false) => execFrom m fuel env' rest
    | (.brk env', _) => some (.brk env')
    | (.cont env', _) => some (.cont env')
termination_by cs => (fuel, sizeOf cs, 0)

/-- Run the statements of one clause, up to a `break`, a `continue` or a
`return`. The flag says whether a `break` ended it: a `break` leaves the
`switch` (ECMA-262 §14.12.4), and a `continue` leaves it for the loop around
it. -/
def execCase (m : Scope) (fuel : Nat) (env : Env N) : List Stmt → Option (Outcome N × Bool)
  | [] => some (.normal env, false)
  | s :: rest =>
    if s matches .breakStmt _ then some (.normal env, true) else do
      -- As in `exec`: an assignment to a `const` throws.
      if s.constAssignedIn rest then none
      match ← execStmt m fuel env s with
      | .ret r => some (.ret r, false)
      | .normal env' => execCase m fuel env' rest
      | .brk env' => some (.normal env', true)
      | .cont env' => some (.cont env', false)
termination_by ss => (fuel, sizeOf ss, 0)

/-- Run the body of a `for … of` loop once for each of `items`, in a new scope
with the names that `bind` gives the item: `[(x, v)]` for `for (const x of …)`,
or the names of a pattern. Each run keeps the changes to outer variables, and
drops those names and the variables the body declares. A `continue` ends one
run, and a `break` ends the loop (`LoopContinues`, ECMA-262 §14.7.1.2). -/
def execLoop (m : Scope) (fuel : Nat) (env : Env N) (bind : Val N → Option (Env N)) (body : Stmt) :
    List (Val N) → Option (Outcome N)
  | [] => some (.normal env)
  | x :: xs => do
    match ← execStmt m fuel ((← bind x) ++ env) body with
    | .ret v => some (.ret v)
    | .normal env' => execLoop m fuel (env'.drop (env'.length - env.length)) bind body xs
    | .cont env' => execLoop m fuel (env'.drop (env'.length - env.length)) bind body xs
    | .brk env' => some (.normal (env'.drop (env'.length - env.length)))
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- Run the body of `for (let name = k; name < b; name++)`, from the value `k`
of `name` on, while `name < b` holds. Each run keeps the changes to outer
variables, and drops `name` and the variables the body declares. A `continue`
ends one run, the update then adds one to `name`, and a `break` ends the
loop. At most `left` runs may come. The model gives no value for a loop that
would go on past them, as one past `Number.MAX_SAFE_INTEGER` would. -/
def execCounted (m : Scope) (fuel : Nat) (env : Env N) (name : String) (body : Stmt) (b : N) (k : Int) :
    Nat → Option (Outcome N)
  | 0 => none
  | left + 1 =>
    if JSNumber.lt (JSNumber.ofSafeInt k) b then do
      match ← execStmt m fuel ((name, .num (JSNumber.ofSafeInt k)) :: env) body with
      | .ret v => some (.ret v)
      | .normal env' => execCounted m fuel (env'.drop (env'.length - env.length)) name body b (k + 1) left
      | .cont env' => execCounted m fuel (env'.drop (env'.length - env.length)) name body b (k + 1) left
      | .brk env' => some (.normal (env'.drop (env'.length - env.length)))
    else some (.normal env)
termination_by left => (fuel, sizeOf body, left + 1)

/-- Run a statement list, up to its end or its first `return`, `break` or
`continue`. -/
def exec (m : Scope) (fuel : Nat) (env : Env N) : List Stmt → Option (Outcome N)
  | [] => some (.normal env)
  | s :: rest => do
    -- An assignment to a `const` throws; the model gives no value then.
    if s.constAssignedIn rest then none
    match ← execStmt m fuel env s with
    | .ret v => some (.ret v)
    | .normal env' => exec m fuel env' rest
    | .brk env' => some (.brk env')
    | .cont env' => some (.cont env')
termination_by ss => (fuel, sizeOf ss, 0)

end

/-- Call the function `key` of `p` with `args`, as a call expression would
(ECMA-262 §10.2.1): bind each parameter to its argument and run the body.
The result is `.ok` of the value that the body returns, or `.error` of the
value that it throws. -/
def callIn (p : Program) (key : DeclRef) (args : List (Val N)) (fuel : Nat := 64) :
    Option (Except (Val N) (Val N)) := do
  let (params, body) ← (functionsOf p).lookup key
  -- As in `evalCall`: the function changes only collections that it owns.
  if !Stmt.ownsChanges params body then none
  match ← execStmt ⟨p, key.file⟩ fuel (← bindArgs params args) body with
  | .ret r => some r
  | .normal _ | .brk _ | .cont _ => none

/-- The value that the call of `key` returns, or none when it throws. -/
def runIn (p : Program) (key : DeclRef) (args : List (Val N)) (fuel : Nat := 64) : Option (Val N) :=
  (callIn p key args fuel).bind Except.toOption

/-- Call the function `name` of the one-file program `m`. -/
def run (m : Module) (name : String) (args : List (Val N)) (fuel : Nat := 64) : Option (Val N) :=
  runIn [("", m)] ⟨"", name⟩ args fuel

end tolean.TypeScript.Eval
