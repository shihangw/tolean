import tolean.TypeScript.Syntax.Ast
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
deriving Inhabited

/-- `ToBoolean` (ECMA-262 §7.1.2), on the values of the subset. A number is
false when it is `+0`, `-0` or `NaN`, and `-0 === 0`. -/
def Val.truthy : Val N → Bool
  | .int i => i != 0
  | .num n => !(JSNumber.isNaN n || JSNumber.eq n (JSNumber.ofSafeInt 0))
  | .bool b => b
  | .str s => !s.isEmpty
  | .null | .undefined => false
  | .list _ | .obj _ => true

/-- The result of `typeof` (ECMA-262 §13.5.3.1) on the values of the
subset. `null` is `"object"`, and so are an array and an object, which are
not callable. -/
def Val.typeOf : Val N → String
  | .int _ => "bigint"
  | .num _ => "number"
  | .bool _ => "boolean"
  | .str _ => "string"
  | .undefined => "undefined"
  | .null | .list _ | .obj _ => "object"

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
  | .undefined, .null | .undefined, .list _ | .undefined, .obj _ => some false
  | .int _, .undefined | .num _, .undefined | .bool _, .undefined | .str _, .undefined
  | .null, .undefined | .list _, .undefined | .obj _, .undefined => some false
  | .null, .int _ | .null, .num _ | .null, .bool _ | .null, .str _ | .null, .list _
  | .null, .obj _ => some false
  | .int _, .null | .num _, .null | .bool _, .null | .str _, .null | .list _, .null
  | .obj _, .null => some false
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
(`BigInt::divide`, `BigInt::remainder`). On numbers, `a > b` is `b < a` and
`a >= b` is `b <= a`, as `IsLessThan` evaluates them (ECMA-262 §13.10.1).
The subset has no `/` or `%` on numbers. -/
def binary : BinOp → Val N → Val N → Option (Val N)
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .div, .int a, .int b => if b == 0 then none else some (.int (a.tdiv b))
  | .mod, .int a, .int b => if b == 0 then none else some (.int (a.tmod b))
  | .lt, .int a, .int b => some (.bool (decide (a < b)))
  | .gt, .int a, .int b => some (.bool (decide (a > b)))
  | .le, .int a, .int b => some (.bool (decide (a ≤ b)))
  | .ge, .int a, .int b => some (.bool (decide (a ≥ b)))
  | .add, .num a, .num b => some (.num (JSNumber.add a b))
  | .sub, .num a, .num b => some (.num (JSNumber.sub a b))
  | .mul, .num a, .num b => some (.num (JSNumber.mul a b))
  | .lt, .num a, .num b => some (.bool (JSNumber.lt a b))
  | .gt, .num a, .num b => some (.bool (JSNumber.lt b a))
  | .le, .num a, .num b => some (.bool (JSNumber.le a b))
  | .ge, .num a, .num b => some (.bool (JSNumber.le b a))
  | .strictEq, a, b => (strictEq a b).map .bool
  | .strictNe, a, b => (strictEq a b).map (.bool ∘ not)
  | .looseEq, a, b => (looseEq a b).map .bool
  | .looseNe, a, b => (looseEq a b).map (.bool ∘ not)
  | _, _, _ => none

/-- The element of the array `items` whose index is the safe integer `i`, or
`undefined` when `i` is none or no index of the array. -/
def elementAt (items : List (Val N)) : Option Int → Val N
  | some i => if 0 ≤ i then items[i.toNat]?.getD .undefined else .undefined
  | none => .undefined

/-- What a statement list does: it runs to its end with the variables it
leaves, or it returns a value, or a `break` or a `continue` ends it with the
variables at that point. These are the completion records of ECMA-262
(§6.2.4) that the subset can make. -/
inductive Outcome (N : Type) where
  | normal (env : Env N)
  | ret (v : Val N)
  | brk (env : Env N)
  | cont (env : Env N)
deriving Inhabited

/-- The text of a number literal. -/
def numberText? : Expr → Option String
  | .number _ text => some text
  | _ => none

/-- The functions of the module, by name. -/
def functions (m : Module) : List (String × List String × Stmt) :=
  m.decls.filterMap fun
    | .function _ _ name _ params _ body => some (name, params.map (·.name), body)
    | _ => none

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
  | .array _ elems => (evalList m fuel env elems).map .list
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
  -- `Number.isNaN(x)`, `Number.isFinite(x)` and `Number.isSafeInteger(x)` on a
  -- number (ECMA-262 §21.1.2), unless a variable hides `Number`.
  | .call _ (.member _ (.ident _ "Number") test) [arg] => do
    if (env.lookup "Number").isSome then none
    let .num n ← eval m fuel env arg | none
    if test == "isNaN" then some (.bool (JSNumber.isNaN n))
    else if test == "isFinite" then some (.bool (JSNumber.isFinite n))
    else if test == "isSafeInteger" then some (.bool (JSNumber.toSafeInt n).isSome)
    else none
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
  -- `xs.map((x, i) => e)`: `map` passes the index too, as a number
  -- (ECMA-262 §23.1.3.21, step 6.c.ii). An array has fewer than 2^32
  -- elements, so the index is a safe integer. Two parameters of one arrow
  -- function may not have the same name (§15.3.1).
  | .call _ (.member _ recv method) [.arrow _ _ [p, q] body] => do
    if method != "map" || p.name == q.name then none
    let .list items ← eval m fuel env recv | none
    return .list (← evalMapIdx m fuel env p.name q.name body 0 items)
  | .call _ (.ident _ name) args => do
    let vs ← evalList m fuel env args
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let key ← resolve m name
      let (params, body) ← (functionsOf m.program).lookup key
      -- A `break` or a `continue` outside a loop is an early error
      -- (ECMA-262 §14.8.1 and §14.9.1), so the model gives no value.
      match ← execStmt { m with file := key.file } fuel (← bindArgs params vs) body with
      | .ret v => some v
      | .normal _ | .brk _ | .cont _ => none
  | _ => none
termination_by e => (fuel, sizeOf e, 0)

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

def evalList (m : Scope) (fuel : Nat) (env : Env N) : List Expr → Option (List (Val N))
  | [] => some []
  | e :: es => do return (← eval m fuel env e) :: (← evalList m fuel env es)
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
    return .normal ((name, ← eval m fuel env init) :: env)
  | .returnStmt _ (some e) => do return .ret (← eval m fuel env e)
  -- `xs.push(v)` adds `v` at the end (`Array.prototype.push`, ECMA-262
  -- §23.1.3.23). The subset pushes only onto an array that the function owns,
  -- which nothing else can see, so the push changes only the variable.
  | .exprStmt _ (.call _ (.member _ (.ident _ name) "push") [arg]) => do
    let .list items ← env.lookup name | none
    return .normal (env.set name (.list (items ++ [← eval m fuel env arg])))
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
  -- `for (const x of xs)` on an array: the body runs once for each element,
  -- in order, with `x` bound to it in a new scope (`ForIn/OfBodyEvaluation`,
  -- ECMA-262 §14.7.5.7, with the array iterator of §23.1.5.1).
  | .forOfStmt _ .const name iterable body => do
    let .list items ← eval m fuel env iterable | none
    execLoop m fuel env name body items
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

/-- Run the body of `for (const name of …)` once for each of `items`. Each
run keeps the changes to outer variables, and drops `name` and the variables
the body declares. A `continue` ends one run, and a `break` ends the loop
(`LoopContinues`, ECMA-262 §14.7.1.2). -/
def execLoop (m : Scope) (fuel : Nat) (env : Env N) (name : String) (body : Stmt) :
    List (Val N) → Option (Outcome N)
  | [] => some (.normal env)
  | x :: xs => do
    match ← execStmt m fuel ((name, x) :: env) body with
    | .ret v => some (.ret v)
    | .normal env' => execLoop m fuel (env'.drop (env'.length - env.length)) name body xs
    | .cont env' => execLoop m fuel (env'.drop (env'.length - env.length)) name body xs
    | .brk env' => some (.normal (env'.drop (env'.length - env.length)))
termination_by xs => (fuel, sizeOf body, xs.length + 1)

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
(ECMA-262 §10.2.1): bind each parameter to its argument, run the body, and
take the value it returns. -/
def runIn (p : Program) (key : DeclRef) (args : List (Val N)) (fuel : Nat := 64) : Option (Val N) := do
  let (params, body) ← (functionsOf p).lookup key
  match ← execStmt ⟨p, key.file⟩ fuel (← bindArgs params args) body with
  | .ret v => some v
  | .normal _ | .brk _ | .cont _ => none

/-- Call the function `name` of the one-file program `m`. -/
def run (m : Module) (name : String) (args : List (Val N)) (fuel : Nat := 64) : Option (Val N) :=
  runIn [("", m)] ⟨"", name⟩ args fuel

end tolean.TypeScript.Eval
