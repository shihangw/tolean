import tolean.Go.Spec.Basic
import tolean.Go.Syntax.Ast
import tolean.Core.Loop
import tolean.Core.Except

/-!
The meaning of the pure Go subset, as an interpreter in Lean.

`eval` and `exec` run the syntax tree that the parser returns, with no
translation in between. `translate_sound` in `tolean/Go/Proof/Package.lean`
proves that when a function that the translator writes as IR gives a value,
this interpreter gives the same value for the same call, and that when it
panics, this interpreter panics too. So a pure function trusts this
interpreter, and no longer the translator.

This file is trusted. Each rule follows the Go specification for the values
that the subset has, and the comments name the section. An expression gives
a `Res`: a value, a panic, or `none` when it leaves the subset. A statement
gives an `Outcome`, which can be a panic too.

The interpreter assumes a program that `go build` accepts. It does not check
types, so it gives a value to some programs that Go refuses, such as
`x := true; x++`. No claim depends on those values, because the translator
refuses such programs.

- `int` and `int64` values are `Int`. Each `+`, `-` and `*` wraps its
  result into the 64-bit range with `wrap64`, as Go's two's-complement
  arithmetic does. So `int` is 64 bits wide, as on every 64-bit platform.
- `/` and `%` on integers panic when the divisor is zero (Go specification,
  "Integer operators" and "Run-time panics"). The panic value is the runtime
  error, which the interpreter models by its message,
  `runtime error: integer divide by zero`.
- A string is a Lean `String`. Go strings are bytes, but `+` and `==` on
  valid UTF-8 agree with `++` and `=` on Lean strings. The interpreter refuses
  the escapes that can make other bytes, such as `\xff`.
-/
namespace tolean.Go.Eval

open tolean.Go.Syntax
open tolean.Core (Res)

/-- A Go value of the subset. -/
inductive Val where
  | int (i : Int)
  | bool (b : Bool)
  | str (s : String)
  /-- A struct: the value of each field, in the order that its type declares
  them (Go specification, "Struct types"). -/
  | strct (fields : List (String × Val))
deriving Inhabited, Repr

mutual

/-- Equality of values. `deriving DecidableEq` does not handle the list of
fields, so it is written out. -/
def Val.decEq : (a b : Val) → Decidable (a = b)
  | .int a, .int b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .bool a, .bool b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .str a, .str b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .strct a, .strct b =>
    match Val.decEqFields a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by simp [h])
  | .int _, .bool _ | .int _, .str _ | .int _, .strct _
  | .bool _, .int _ | .bool _, .str _ | .bool _, .strct _
  | .str _, .int _ | .str _, .bool _ | .str _, .strct _
  | .strct _, .int _ | .strct _, .bool _ | .strct _, .str _ => isFalse (by simp)

def Val.decEqFields : (a b : List (String × Val)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by simp)
  | (n, v) :: a, (m, w) :: b =>
    if hn : n = m then
      match Val.decEq v w, Val.decEqFields a b with
      | isTrue hv, isTrue ha => isTrue (by rw [hn, hv, ha])
      | isFalse hv, _ => isFalse (by simp [hv])
      | _, isFalse ha => isFalse (by simp [ha])
    else isFalse (by simp [hn])

end

instance : DecidableEq Val := Val.decEq

/-- The variables in scope, innermost first. -/
abbrev Env := List (String × Val)

/-- Change the innermost variable named `name`. -/
def Env.set (env : Env) (name : String) (v : Val) : Env :=
  match env with
  | [] => []
  | (n, old) :: rest => if n == name then (n, v) :: rest else (n, old) :: Env.set rest name v

/-! ### Literals -/

/-- The value of one digit, or 99 for a character that is no digit. -/
def digitValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 99

/-- The value of a nonempty list of digits in base `radix`. -/
def digitsIn (radix : Nat) (digits : List Char) : Option Nat :=
  if digits.isEmpty then none
  else digits.foldlM (fun acc c =>
    let d := digitValue c
    if d < radix then some (acc * radix + d) else none) 0

/-- The value of an integer literal (Go specification, "Integer literals").
An `_` may stand between digits. `0x`, `0b` and `0o` start a hexadecimal,
binary or octal literal, and a `0` before more digits starts an octal one. -/
def intLit? (raw : String) : Option Int :=
  match raw.toList.filter (· != '_') with
  | '0' :: 'x' :: ds | '0' :: 'X' :: ds => Int.ofNat <$> digitsIn 16 ds
  | '0' :: 'b' :: ds | '0' :: 'B' :: ds => Int.ofNat <$> digitsIn 2 ds
  | '0' :: 'o' :: ds | '0' :: 'O' :: ds => Int.ofNat <$> digitsIn 8 ds
  | '0' :: d :: ds => Int.ofNat <$> digitsIn 8 (d :: ds)
  | ds => Int.ofNat <$> digitsIn 10 ds

/-- The characters of an interpreted string literal after its escapes, or
none for an escape that the subset leaves out (Go specification, "String
literals"). The octal, `\x`, `\u` and `\U` escapes are left out, because the
first two can make bytes that are not UTF-8. `\'` is valid only in a rune
literal, so Go refuses it in a string. -/
def unescape : List Char → Option (List Char)
  | [] => some []
  | '\\' :: c :: rest => do
    let e ← match c with
      | 'a' => some (Char.ofNat 7)
      | 'b' => some (Char.ofNat 8)
      | 'f' => some (Char.ofNat 12)
      | 'n' => some '\n'
      | 'r' => some '\r'
      | 't' => some '\t'
      | 'v' => some (Char.ofNat 11)
      | '\\' => some '\\'
      | '"' => some '"'
      | _ => none
    return e :: (← unescape rest)
  | '\\' :: [] => none
  | c :: rest => do return c :: (← unescape rest)

/-- The value of a string literal (Go specification, "String literals"). A
raw literal, in backquotes, holds its text without the carriage returns. -/
def stringLit? (raw : String) : Option String :=
  match raw.toList with
  | '`' :: rest => some (String.ofList (rest.dropLast.filter (· != '\r')))
  | '"' :: rest => String.ofList <$> unescape rest.dropLast
  | _ => none

/-! ### Operators -/

/-- A binary operator of the subset. -/
inductive BinOp where
  | add | sub | mul | quo | rem | eq | ne | lt | le | gt | ge | land | lor
deriving DecidableEq, Repr, Inhabited

def BinOp.ofString? : String → Option BinOp
  | "+" => some .add | "-" => some .sub | "*" => some .mul
  | "/" => some .quo | "%" => some .rem
  | "==" => some .eq | "!=" => some .ne
  | "<" => some .lt | "<=" => some .le | ">" => some .gt | ">=" => some .ge
  | "&&" => some .land | "||" => some .lor
  | _ => none

/-- `==` on two values of the same type (Go specification, "Comparison
operators"). -/
def eqVal : Val → Val → Option Bool
  | .int a, .int b => some (decide (a = b))
  | .bool a, .bool b => some (decide (a = b))
  | .str a, .str b => some (decide (a = b))
  | _, _ => none

/-- The bytes of a string (Go specification, "String types"): a Go string is
a sequence of bytes, and the bytes of a Lean `String` are its UTF-8
encoding. -/
def strBytes (s : String) : List UInt8 := s.toUTF8.toList

/-- A binary operator on the values of its operands (Go specification,
"Arithmetic operators" and "Comparison operators"). Integer `+`, `-` and `*`
wrap, and `+` on strings joins them. `&&` and `||` evaluate their right
operand only when they need it, so `eval` runs them itself, and this gives
their value once both operands have one. -/
def binary : BinOp → Val → Val → Option Val
  | .add, .int a, .int b => some (.int (wrap64 (a + b)))
  | .add, .str a, .str b => some (.str (a ++ b))
  | .sub, .int a, .int b => some (.int (wrap64 (a - b)))
  | .mul, .int a, .int b => some (.int (wrap64 (a * b)))
  | .eq, a, b => (eqVal a b).map .bool
  | .ne, a, b => (eqVal a b).map (.bool ∘ not)
  | .lt, .int a, .int b => some (.bool (decide (a < b)))
  | .le, .int a, .int b => some (.bool (decide (a ≤ b)))
  | .gt, .int a, .int b => some (.bool (decide (a > b)))
  | .ge, .int a, .int b => some (.bool (decide (a ≥ b)))
  -- Strings are ordered lexically, byte by byte (Go specification,
  -- "Comparison operators").
  | .lt, .str a, .str b => some (.bool (decide (strBytes a < strBytes b)))
  | .le, .str a, .str b => some (.bool (decide (strBytes a ≤ strBytes b)))
  | .gt, .str a, .str b => some (.bool (decide (strBytes a > strBytes b)))
  | .ge, .str a, .str b => some (.bool (decide (strBytes a ≥ strBytes b)))
  | .land, .bool a, .bool b => some (.bool (a && b))
  | .lor, .bool a, .bool b => some (.bool (a || b))
  | _, _, _ => none

/-- The value of the run-time panic that an integer division by zero causes
(Go specification, "Run-time panics"). Go panics with a `runtime.Error`, and
the interpreter models it by the text of its `Error` method. -/
def divideByZero : Val := .str "runtime error: integer divide by zero"

/-- A binary operator on the values of its operands, which can panic (Go
specification, "Integer operators"). `/` truncates toward zero and `%` takes
the sign of the dividend, as `Int.tdiv` and `Int.tmod` do. A zero divisor
panics. The quotient of the most negative value and `-1` overflows, and it
wraps to the most negative value, as `wrap64` does. The remainder never
overflows. The other operators are `binary`. -/
def operate : BinOp → Val → Val → Res Val Val
  | .quo, .int a, .int b =>
    if b = 0 then .fail divideByZero else .ok (.int (wrap64 (a.tdiv b)))
  | .rem, .int a, .int b =>
    if b = 0 then .fail divideByZero else .ok (.int (a.tmod b))
  | o, a, b => Res.lift (binary o a b)

/-- The run-time panic of an index `i` out of the range of a string of `n`
bytes (Go specification, "Index expressions" and "Run-time panics"). The
interpreter models it by the text of its `Error` method, which leaves out
the length when the index is negative. -/
def indexOutOfRange (i : Int) (n : Nat) : Val :=
  .str ("runtime error: index out of range [" ++
    (if i < 0 then s!"{i}]" else s!"{i}] with length {n}"))

/-- `s[i]` on a string (Go specification, "Index expressions"): the byte at
index `i`, of type `byte`, which the interpreter holds as an integer. An
index out of range panics. -/
def indexString : Val → Val → Res Val Val
  | .str s, .int i =>
    if h : 0 ≤ i ∧ i.toNat < (strBytes s).length then .ok (.int (strBytes s)[i.toNat].toNat)
    else .fail (indexOutOfRange i (strBytes s).length)
  | _, _ => none

/-- A predeclared function of the subset: `len`, and the conversions to
`int` and `int64`. -/
inductive Builtin where
  | len | toInt | toInt64
deriving DecidableEq, Repr

/-- A predeclared function on the value of its argument. `len` of a string is
its number of bytes (Go specification, "Length and capacity"). A conversion
of an integer to `int` or `int64` keeps its value, because every integer
type of the subset fits in 64 bits (Go specification, "Conversions"). Go
refuses a conversion of a `bool` or a `string` to an integer type, so the
interpreter keeps any value, as it does for other programs that Go
refuses. -/
def applyBuiltin : Builtin → Val → Option Val
  | .len, .str s => some (.int (strBytes s).length)
  | .len, _ => none
  | .toInt, v => some v
  | .toInt64, v => some v

/-- A unary operator on the value of its operand. `-` wraps, as `0 - x`
does. -/
def unary : String → Val → Option Val
  | "-", .int i => some (.int (wrap64 (-i)))
  | "!", .bool b => some (.bool !b)
  | _, _ => none

/-- What an assignment operator does (Go specification, "Assignment
statements"): `:=` declares, `=` assigns, and `x op= y` assigns `x op y`. -/
inductive AssignKind where
  | define | assign
  | compound (op : BinOp)
deriving DecidableEq, Repr

def AssignKind.ofString? : String → Option AssignKind
  | ":=" => some .define | "=" => some .assign
  | "+=" => some (.compound .add) | "-=" => some (.compound .sub)
  | "*=" => some (.compound .mul)
  | "/=" => some (.compound .quo) | "%=" => some (.compound .rem)
  | _ => none

/-- `x++` is `x += 1`, and `x--` is `x -= 1` (Go specification, "IncDec
statements"). -/
def incDecOp? : String → Option BinOp
  | "++" => some .add | "--" => some .sub
  | _ => none

/-! ### Programs -/

/-- What a statement list does: it runs to its end with the variables it
leaves, it returns a value, or it panics with a value. -/
inductive Outcome where
  | normal (env : Env)
  | ret (v : Val)
  | panic (v : Val)
deriving Inhabited

/-- A loop ends the function both when its body returns and when it panics,
so the shared loop runner carries both as its return value: `.ok` for a
return and `.error` for a panic. -/
def Outcome.toLoop : Outcome → tolean.Core.Loop.Outcome Env (Except Val Val)
  | .normal env => .normal env
  | .ret value => .ret (.ok value)
  | .panic value => .ret (.error value)

def Outcome.fromLoop : tolean.Core.Loop.Outcome Env (Except Val Val) → Option Outcome
  | .normal env => some (.normal env)
  | .ret (.ok value) => some (.ret value)
  | .ret (.error value) => some (.panic value)
  | _ => none

/-- Run `k` on the value of an expression. When the expression panics, the
statement panics with the same value. -/
def withValue (r : Res Val Val) (k : Val → Option Outcome) : Option Outcome :=
  match r with
  | none => none
  | some (.error x) => some (.panic x)
  | some (.ok v) => k v

@[simp] theorem withValue_ok (v : Val) (k : Val → Option Outcome) :
    withValue (some (.ok v)) k = k v := rfl

@[simp] theorem withValue_error (x : Val) (k : Val → Option Outcome) :
    withValue (some (.error x)) k = some (.panic x) := rfl

@[simp] theorem withValue_none (k : Val → Option Outcome) : withValue none k = none := rfl

/-- A finite counted head with literal bounds. The strict bound keeps the
last increment within Go's signed 64-bit range. -/
def countedHead : Option Stmt → Option Expr → Option Stmt → Option (String × List Val)
  | some (.assign _ ":=" [.ident _ index] [.lit _ .int start]),
      some (.binary _ "<" (.ident _ test) (.lit _ .int stop)),
      some (.incDec _ "++" (.ident _ step)) => do
    if index != test || index != step then none
    let a ← intLit? start
    let b ← intLit? stop
    if a < 0 || b < 0 || a ≥ 2 ^ 63 || b ≥ 2 ^ 63 then none
    if (b - a).toNat > 256 then none
    return (index, (List.range' a.toNat (b - a).toNat).map (fun n => .int (Int.ofNat n)))
  | _, _, _ => none

mutual

/-- This subset does not allow the body to change or shadow the counter.
It also excludes nested loops until their frame proof is available. -/
def countedBodySafe (index : String) : Stmt → Bool
  | .assign _ _ [.ident _ name] [_] => name != index
  | .incDec _ _ (.ident _ name) => name != index
  | .ret _ _ => true
  | .block _ ss => countedStatementsSafe index ss
  | .ifStmt _ none _ t none => countedBodySafe index t
  | .ifStmt _ none _ t (some e) => countedBodySafe index t && countedBodySafe index e
  | .decl _ (.mk _ "var" [.value _ [name] _ _]) => name != index
  | _ => false

def countedStatementsSafe (index : String) : List Stmt → Bool
  | [] => true
  | s :: ss => countedBodySafe index s && countedStatementsSafe index ss

end

/-- The functions of a package and the names it declares at the top level. -/
structure Program where
  /-- Each function without a receiver: its name, the names of its
  parameters in order, and its body. -/
  funcs : List (String × List String × Stmt)
  /-- The names that the package or its imports declare. A name such as
  `int` or `true` is predeclared only when the package does not declare it. -/
  names : List String
  /-- Each package-level constant that the subset models: its name, its type
  when the declaration names one, and its value. -/
  consts : List (String × Option Expr × Val) := []
  /-- Each struct type that the package declares: its name, and the name and
  type of each field, in order. -/
  structs : List (String × List (String × Expr)) := []

/-- The names of the parameters, in order. A parameter without a name, as in
`func f(int) int`, still takes an argument, and its name is `_`, which no
code can read. -/
def paramNames (fields : List Field) : List String :=
  fields.flatMap fun
    | .mk _ [] _ _ => ["_"]
    | .mk _ names _ _ => names

/-- The last part of an import path, without the quotes of its literal. The
quotes are dropped character by character rather than with `String.replace`.
In Lean 4.30, `replace` with a string pattern compiles to a call of a
standard library helper that the WebAssembly build of the library does not
have, so the playground's translator would not link. -/
def importName (raw : String) : String :=
  String.ofList (((raw.splitOn "/").getLast?.getD raw).toList.filter (· != '"'))

/-- The names that one top-level declaration binds. `init` and `_` bind
nothing, and a method binds no package name. An import binds its name, or the
last part of its path, which is all a file can use to name it. -/
def declNames : Decl → List String
  | .func _ none name .. => if name == "init" || name == "_" then [] else [name]
  | .func _ (some _) .. => []
  | .gen (.mk _ _ specs) => specs.flatMap fun
    | .type _ name _ _ => [name]
    | .value _ names _ _ => names
    | .import _ raw alias => alias.toList ++ [importName raw]

/-- The function `f` of the declarations, as a call of `f` finds it. -/
def funcOf : Decl → Option (String × List String × Stmt)
  | .func _ none name params _ body =>
    if name == "init" || name == "_" then none else some (name, paramNames params, body)
  | _ => none

/-- The value of a predeclared name, unless the package declares it. -/
def predeclared (p : Program) (name : String) : Option Val :=
  if p.names.contains name then none
  else match name with
    | "true" => some (.bool true)
    | "false" => some (.bool false)
    | _ => none

/-- The predeclared function that the name `f` calls, unless the package
declares the name (Go specification, "Predeclared identifiers"). -/
def builtin (p : Program) (f : String) : Option Builtin :=
  if p.names.contains f then none
  else match f with
    | "len" => some .len
    | "int" => some .toInt
    | "int64" => some .toInt64
    | _ => none

/-- The value of a constant's expression (Go specification, "Constants" and
"Constant declarations"): an integer or string literal, an integer literal
after `-`, or `true` or `false` when the package does not declare the name.
`names` holds the names that the package declares. Any other constant
expression, such as one that uses `iota` or another constant, leaves the
subset. A typed constant has the value of its expression, because `go build`
refuses one whose value its type cannot represent. -/
def constValue? (names : List String) : Expr → Option Val
  | .lit _ .int raw => (.int ·) <$> intLit? raw
  | .lit _ .string raw => (.str ·) <$> stringLit? raw
  | .unary _ "-" (.lit _ .int raw) => (fun n => .int (-n)) <$> intLit? raw
  | .paren _ e => constValue? names e
  | .ident _ name =>
    if names.contains name then none
    else match name with
      | "true" => some (.bool true)
      | "false" => some (.bool false)
      | _ => none
  | _ => none

/-- The constants of one top-level declaration that the subset models: a
`const` spec that declares one name with one value. A spec without a value
repeats the one before it, with `iota`, so it leaves the subset. -/
def declConsts (names : List String) : Decl → List (String × Option Expr × Val)
  | .gen (.mk _ "const" specs) => specs.filterMap fun
    | .value _ [x] type [e] => (fun v => (x, type, v)) <$> constValue? names e
    | _ => none
  | _ => []

/-- The fields of a struct type, each with its own name (Go specification,
"Struct types"): `X, Y int` declares two. An embedded field has no name of
its own, so a struct with one leaves the subset, as does one whose field
names repeat, which Go refuses. -/
def structFields (fields : List Field) : Option (List (String × Expr)) := do
  let fs ← fields.mapM fun
    | .mk _ [] _ _ => none
    | .mk _ names type _ => some (names.map (·, type))
  let fs := fs.flatten
  if (fs.map (·.1)).Nodup then some fs else none

/-- The struct types of one top-level declaration (Go specification, "Type
declarations"): `type S struct { … }`. -/
def declStructs : Decl → List (String × List (String × Expr))
  | .gen (.mk _ "type" specs) => specs.filterMap fun
    | .type _ x (.structType _ fields) false => (x, ·) <$> structFields fields
    | _ => none
  | _ => []

/-- The program of the declarations of a package's files. -/
def program (decls : List Decl) : Program where
  funcs := decls.filterMap funcOf
  names := decls.flatMap declNames
  consts := decls.flatMap (declConsts (decls.flatMap declNames))
  structs := decls.flatMap declStructs

/-- The value of a package-level name that no variable hides: a constant of
the package, or a predeclared name that the package does not declare (Go
specification, "Declarations and scope"). -/
def global (p : Program) (name : String) : Option Val :=
  match p.consts.lookup name with
  | some (_, v) => some v
  | none => predeclared p name

/-- The zero value of a predeclared type of the subset, unless the package
declares the name. -/
def basicZeroOf (p : Program) : Expr → Option Val
  | .ident _ name =>
    if p.names.contains name then none
    else match name with
      | "int" | "int64" => some (.int 0)
      | "bool" => some (.bool false)
      | "string" => some (.str "")
      | _ => none
  | _ => none

/-- The zero value of a type (Go specification, "The zero value"). A struct's
is the zero value of each field, and the subset's fields have predeclared
types. -/
def zeroOf (p : Program) (te : Expr) : Option Val :=
  match te with
  | .ident _ name =>
    match p.structs.lookup name with
    | some fields => (.strct ·) <$> fields.mapM fun (f, t) => (f, ·) <$> basicZeroOf p t
    | none => basicZeroOf p te
  | _ => none

/-- The element of a composite literal without its key. -/
def elemValue : Expr → Expr
  | .keyValue _ _ v => v
  | e => e

/-- The field that a key of a struct literal names. -/
def keyName? : Expr → Option String
  | .keyValue _ (.ident _ f) _ => some f
  | _ => none

/-- The value of a struct literal of a type with `fields`, whose elements
`elts` have the values `vals` (Go specification, "Composite literals"). The
elements are all keyed or none is. A keyed literal gives each field it names
its element's value and the others their zero value, and every key must name
a field once. One without keys gives every field in order. -/
def structLit (p : Program) (fields : List (String × Expr)) (elts : List Expr) (vals : List Val) :
    Option Val :=
  if elts.all (keyName? · |>.isSome) then do
    let keys ← elts.mapM keyName?
    unless keys.Nodup && keys.all (fields.lookup · |>.isSome) do none
    let given := keys.zip vals
    return .strct (← fields.mapM fun (f, t) =>
      match given.lookup f with
      | some v => some (f, v)
      | none => (f, ·) <$> basicZeroOf p t)
  else if elts.any (keyName? · |>.isSome) || vals.length != fields.length then none
  else some (.strct ((fields.map (·.1)).zip vals))

/-- The field `f` of a struct (Go specification, "Selectors"). -/
def fieldOf (v : Val) (f : String) : Option Val :=
  match v with
  | .strct fs => fs.lookup f
  | _ => none

/-- A struct with the field `f` set to `w`. -/
def setField (v : Val) (f : String) (w : Val) : Option Val :=
  match v with
  | .strct fs => if (fs.lookup f).isSome then some (.strct (fs.map fun (g, u) => (g, if g == f then w else u))) else none
  | _ => none

/-- Every statement has a positive size, so that a statement with an init
statement is larger than the same statement without it. -/
theorem stmt_size_pos (s : Stmt) : 0 < sizeOf s := by
  cases s <;> simp <;> omega

mutual

/-- The value of `e`. `fuel` bounds the depth of nested calls, so that the
interpreter is a total function. Operands are evaluated from left to right
(Go specification, "Order of evaluation"), and a panic in one ends the
evaluation. -/
def eval (p : Program) (fuel : Nat) (env : Env) : Expr → Res Val Val
  -- A variable hides a constant of the package and a predeclared name (Go
  -- specification, "Declarations and scope").
  | .ident _ name =>
    match env.lookup name with
    | some v => .ok v
    | none => Res.lift (global p name)
  | .lit _ .int raw => Res.lift (do return .int (← intLit? raw))
  | .lit _ .string raw => Res.lift (do return .str (← stringLit? raw))
  | .paren _ e => eval p fuel env e
  | .unary _ op a => (eval p fuel env a).andThen fun x => Res.lift (unary op x)
  -- `&&` and `||` evaluate the right operand only when the left one does
  -- not decide the result (Go specification, "Logical operators").
  | .binary _ op l r =>
    match BinOp.ofString? op with
    | some .land =>
      (eval p fuel env l).andThen fun
        | .bool true => (eval p fuel env r).andThen fun
          | .bool y => .ok (.bool y)
          | _ => none
        | .bool false => .ok (.bool false)
        | _ => none
    | some .lor =>
      (eval p fuel env l).andThen fun
        | .bool true => .ok (.bool true)
        | .bool false => (eval p fuel env r).andThen fun
          | .bool y => .ok (.bool y)
          | _ => none
        | _ => none
    | some o => (eval p fuel env l).andThen fun x => (eval p fuel env r).andThen fun y => operate o x y
    | none => none
  -- `s[i]` (Go specification, "Index expressions"): `s` and `i` are
  -- evaluated in order, then the index is checked.
  | .index _ s i =>
    (eval p fuel env s).andThen fun x => (eval p fuel env i).andThen fun y => indexString x y
  -- A call of a predeclared function, `len` or a conversion, which takes
  -- one argument, or of a function of the package. A variable of the same
  -- name would hide the function, and the subset has no function values.
  | .call _ (.ident _ f) args false =>
    if (env.lookup f).isSome then none
    else match builtin p f with
      | some b =>
        match args with
        | [a] => (eval p fuel env a).andThen fun x => Res.lift (applyBuiltin b x)
        | _ => none
      | none => callFunc p fuel env f args
  -- `x.f` reads the field `f` of the struct `x`.
  | .selector _ x f => (eval p fuel env x).andThen fun v => Res.lift (fieldOf v f)
  -- `T{…}`: the elements are evaluated in order (Go specification, "Order
  -- of evaluation"), then the struct is built.
  | .composite _ (some (.ident _ t)) elts =>
    match p.structs.lookup t with
    | some fields => (evalElems p fuel env elts).andThen fun vs => Res.lift (structLit p fields elts vs)
    | none => none
  | _ => none
termination_by e => (fuel, sizeOf e, 0)

/-- A call of the function `f` of the package (Go specification, "Calls"):
the arguments are evaluated in order, each parameter is a new variable bound
to its argument, and the body runs. A panic in the body is a panic of the
call (Go specification, "Handling panics"), because the subset has no
`recover`. -/
def callFunc (p : Program) (fuel : Nat) (env : Env) (f : String) (args : List Expr) : Res Val Val :=
    (evalList p fuel env args).andThen fun vs =>
      match fuel with
      | 0 => none
      | fuel + 1 =>
        match p.funcs.lookup f with
        | none => none
        | some (params, body) =>
          if params.length != vs.length then none
          else match execStmt p fuel (params.zip vs).reverse body with
            | some (.ret v) => .ok v
            | some (.panic x) => .fail x
            | _ => none
termination_by (fuel, sizeOf args, 1)

def evalList (p : Program) (fuel : Nat) (env : Env) : List Expr → Res Val (List Val)
  | [] => .ok []
  | e :: es => (eval p fuel env e).andThen fun v => (evalList p fuel env es).andThen fun vs => .ok (v :: vs)
termination_by es => (fuel, sizeOf es, 0)

/-- The values of the elements of a composite literal, in order, without
their keys. -/
def evalElems (p : Program) (fuel : Nat) (env : Env) : List Expr → Res Val (List Val)
  | [] => .ok []
  | .keyValue _ _ v :: es => (eval p fuel env v).andThen fun x =>
    (evalElems p fuel env es).andThen fun xs => .ok (x :: xs)
  | e :: es => (eval p fuel env e).andThen fun x =>
    (evalElems p fuel env es).andThen fun xs => .ok (x :: xs)
termination_by es => (fuel, sizeOf es, 0)

def execStmt (p : Program) (fuel : Nat) (env : Env) : Stmt → Option Outcome
  | .ret _ [e] => withValue (eval p fuel env e) fun v => some (.ret v)
  | .assign _ op [.ident _ x] [e] =>
    match AssignKind.ofString? op with
    -- `x := e` declares `x` in the innermost scope.
    | some .define => withValue (eval p fuel env e) fun v => some (.normal ((x, v) :: env))
    -- `x = e` changes the innermost variable `x`.
    | some .assign =>
      withValue (eval p fuel env e) fun v => do
        let _ ← env.lookup x
        return .normal (env.set x v)
    -- `x op= e` is `x = x op e`, with `x` evaluated once.
    | some (.compound o) =>
      match env.lookup x with
      | none => none
      | some old =>
        withValue ((eval p fuel env e).andThen fun v => operate o old v) fun w =>
          some (.normal (env.set x w))
    | none => none
  -- `x.f = e`: `e` is evaluated, then the field `f` of the variable `x`
  -- changes (Go specification, "Assignment statements").
  | .assign _ "=" [.selector _ (.ident _ x) f] [e] =>
    withValue (eval p fuel env e) fun v => do
      let old ← env.lookup x
      return .normal (env.set x (← setField old f v))
  | .incDec _ op (.ident _ x) => do
    let o ← incDecOp? op
    let old ← env.lookup x
    return .normal (env.set x (← binary o old (.int 1)))
  -- `var x T = e` and `var x T` (Go specification, "Variable
  -- declarations"): without a value, `x` starts at the zero value of `T`.
  | .decl _ (.mk _ "var" [.value _ [x] (some type) values]) =>
    match values with
    | [e] => withValue (eval p fuel env e) fun v => some (.normal ((x, v) :: env))
    | [] => do return .normal ((x, ← zeroOf p type) :: env)
    | _ => none
  -- `if c { … } else …` (Go specification, "If statements"). Each branch is
  -- a block, so what it declares goes out of scope at its end.
  -- `if s; c { … } else …` (Go specification, "If statements"): the simple
  -- statement `s` runs first, and the `if` is its own implicit block, so what
  -- `s` declares goes out of scope at the end of the `if`.
  | .ifStmt sp (some s) c t els => do
    match ← execStmt p fuel env s with
    | .ret v => some (.ret v)
    | .panic x => some (.panic x)
    | .normal env1 =>
      have := stmt_size_pos s
      match ← execStmt p fuel env1 (.ifStmt sp none c t els) with
      | .ret v => some (.ret v)
      | .panic x => some (.panic x)
      | .normal env' => some (.normal (env'.drop (env'.length - env.length)))
  | .ifStmt _ none c t els =>
    withValue (eval p fuel env c) fun
      | .bool b => do
        let out ← if b then execStmt p fuel env t
          else match els with
            | some f => execStmt p fuel env f
            | none => some (.normal env)
        match out with
        | .ret v => some (.ret v)
        | .panic x => some (.panic x)
        | .normal env' => some (.normal (env'.drop (env'.length - env.length)))
      | _ => none
  -- `switch s; x { case a, b: … default: … }` (Go specification, "Switch
  -- statements"). The simple statement `s` runs first, in the implicit block
  -- of the `switch`.
  | .switchStmt sp (some s) tag bsp clauses => do
    match ← execStmt p fuel env s with
    | .ret v => some (.ret v)
    | .panic x => some (.panic x)
    | .normal env1 =>
      have := stmt_size_pos s
      match ← execStmt p fuel env1 (.switchStmt sp none tag bsp clauses) with
      | .ret v => some (.ret v)
      | .panic x => some (.panic x)
      | .normal env' => some (.normal (env'.drop (env'.length - env.length)))
  -- The switch expression is evaluated exactly once, and a missing one stands
  -- for the boolean value `true`. Each clause is an implicit block, so what
  -- it declares goes out of scope at its end. The subset has no
  -- `fallthrough`: the parser refuses it.
  | .switchStmt _ none tag _ clauses =>
    withValue (match tag with
        | none => Res.ok (.bool true)
        | some x => eval p fuel env x) fun v => do
      match ← execClauses p fuel env v clauses none with
      | .ret v => some (.ret v)
      | .panic x => some (.panic x)
      | .normal env' => some (.normal (env'.drop (env'.length - env.length)))
  | .block _ body => do
    match ← exec p fuel env body with
    | .ret v => some (.ret v)
    | .panic x => some (.panic x)
    | .normal env' => some (.normal (env'.drop (env'.length - env.length)))
  -- Go specification, "For statements with for clause". The body cannot
  -- change the counter, and literal bounds cannot change between iterations.
  | .forStmt _ init cond post (.block span body) => do
    let (index, items) ← countedHead init cond post
    if !countedBodySafe index (.block span body) then none
    let out ← tolean.Core.Loop.execLoop
      (fun inner => (exec p fuel inner body).map Outcome.toLoop)
      (fun value outer => some ((index, value) :: outer))
      (fun outer inner => some (inner.drop (inner.length - outer.length))) env items
    match out with
    | .normal inner => some (.normal inner)
    | .ret (.ok value) => some (.ret value)
    | .ret (.error value) => some (.panic value)
    | _ => none
  | _ => none
termination_by s => (fuel, sizeOf s, 0)

/-- The clauses of an expression switch whose switch expression has the
value `v` (Go specification, "Expression switches"). The case expressions are
evaluated left to right and top to bottom, and the first one that equals `v`
picks its clause. When none does, the `default` clause runs, wherever it
stands. `dflt` is the body of the `default` clause seen so far. A panic in a
case expression is a panic of the switch. -/
def execClauses (p : Program) (fuel : Nat) (env : Env) (v : Val) :
    List CaseClause → Option (List Stmt) → Option Outcome
  | [], none => some (.normal env)
  | [], some body => exec p fuel env body
  | .mk _ none body :: rest, _ => execClauses p fuel env v rest (some body)
  | .mk _ (some es) body :: rest, dflt =>
    match matchAny p fuel env v es with
    | none => none
    | some (.error x) => some (.panic x)
    | some (.ok true) => exec p fuel env body
    | some (.ok false) => execClauses p fuel env v rest dflt
termination_by cs dflt => (fuel, sizeOf cs + sizeOf dflt, 0)

/-- Some case expression of `es` equals `v`. They are evaluated in order,
until one does. -/
def matchAny (p : Program) (fuel : Nat) (env : Env) (v : Val) : List Expr → Res Val Bool
  | [] => Res.ok false
  | e :: es => (eval p fuel env e).andThen fun w =>
    match eqVal v w with
    | none => none
    | some true => Res.ok true
    | some false => matchAny p fuel env v es
termination_by es => (fuel, sizeOf es, 0)

/-- Run statements in order, until one returns or panics. -/
def exec (p : Program) (fuel : Nat) (env : Env) : List Stmt → Option Outcome
  | [] => some (.normal env)
  | s :: rest => do
    match ← execStmt p fuel env s with
    | .ret v => some (.ret v)
    | .panic x => some (.panic x)
    | .normal env' => exec p fuel env' rest
termination_by ss => (fuel, sizeOf ss, 0)

end

/-- Call the function `name` of `p` with `args`, as a call expression
would: `.ok` of the value it returns, or `.error` of the value it panics
with. -/
def runIn (p : Program) (name : String) (args : List Val) (fuel : Nat := 64) :
    Option (Except Val Val) := do
  let (params, body) ← p.funcs.lookup name
  if params.length != args.length then none
  match ← execStmt p fuel (params.zip args).reverse body with
  | .ret v => some (.ok v)
  | .panic x => some (.error x)
  | .normal _ => none

end tolean.Go.Eval
