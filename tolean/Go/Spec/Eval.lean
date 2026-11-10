import tolean.Go.Spec.Basic
import tolean.Go.Syntax.Ast

/-!
The meaning of the pure Go subset, as an interpreter in Lean.

`eval` and `exec` run the syntax tree that the parser returns, with no
translation in between. `translate_sound` in `tolean/Go/Proof/Package.lean`
proves that when a function that the translator writes as IR gives a value,
this interpreter gives the same value for the same call. So a pure function
trusts this interpreter, and no longer the translator.

This file is trusted. Each rule follows the Go specification for the values
that the subset has, and the comments name the section. A rule returns
`none` when the program would panic or when it leaves the subset.

The interpreter assumes a program that `go build` accepts. It does not check
types, so it gives a value to some programs that Go refuses, such as
`x := true; x++`. No claim depends on those values, because the translator
refuses such programs.

- `int` and `int64` values are `Int`. Each `+`, `-` and `*` wraps its
  result into the 64-bit range with `wrap64`, as Go's two's-complement
  arithmetic does. So `int` is 64 bits wide, as on every 64-bit platform.
- A string is a Lean `String`. Go strings are bytes, but `+` and `==` on
  valid UTF-8 agree with `++` and `=` on Lean strings. The interpreter refuses
  the escapes that can make other bytes, such as `\xff`.
-/
namespace tolean.Go.Eval

open tolean.Go.Syntax

/-- A Go value of the subset. -/
inductive Val where
  | int (i : Int)
  | bool (b : Bool)
  | str (s : String)
deriving Inhabited, DecidableEq, Repr

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
  | add | sub | mul | eq | ne | lt | le | gt | ge | land | lor
deriving DecidableEq, Repr, Inhabited

def BinOp.ofString? : String → Option BinOp
  | "+" => some .add | "-" => some .sub | "*" => some .mul
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
  | .land, .bool a, .bool b => some (.bool (a && b))
  | .lor, .bool a, .bool b => some (.bool (a || b))
  | _, _, _ => none

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
  | _ => none

/-- `x++` is `x += 1`, and `x--` is `x -= 1` (Go specification, "IncDec
statements"). -/
def incDecOp? : String → Option BinOp
  | "++" => some .add | "--" => some .sub
  | _ => none

/-! ### Programs -/

/-- What a statement list does: it runs to its end with the variables it
leaves, or it returns a value. -/
inductive Outcome where
  | normal (env : Env)
  | ret (v : Val)
deriving Inhabited

/-- The functions of a package and the names it declares at the top level. -/
structure Program where
  /-- Each function without a receiver: its name, the names of its
  parameters in order, and its body. -/
  funcs : List (String × List String × Stmt)
  /-- The names that the package or its imports declare. A name such as
  `int` or `true` is predeclared only when the package does not declare it. -/
  names : List String

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

/-- The program of the declarations of a package's files. -/
def program (decls : List Decl) : Program where
  funcs := decls.filterMap funcOf
  names := decls.flatMap declNames

/-- The value of a predeclared name, unless the package declares it. -/
def predeclared (p : Program) (name : String) : Option Val :=
  if p.names.contains name then none
  else match name with
    | "true" => some (.bool true)
    | "false" => some (.bool false)
    | _ => none

/-- The zero value of a type (Go specification, "The zero value"). -/
def zeroOf (p : Program) : Expr → Option Val
  | .ident _ name =>
    if p.names.contains name then none
    else match name with
      | "int" | "int64" => some (.int 0)
      | "bool" => some (.bool false)
      | "string" => some (.str "")
      | _ => none
  | _ => none

mutual

/-- The value of `e`. `fuel` bounds the depth of nested calls, so that the
interpreter is a total function. -/
def eval (p : Program) (fuel : Nat) (env : Env) : Expr → Option Val
  -- A variable hides a predeclared name (Go specification, "Declarations
  -- and scope").
  | .ident _ name =>
    match env.lookup name with
    | some v => some v
    | none => predeclared p name
  | .lit _ .int raw => do return .int (← intLit? raw)
  | .lit _ .string raw => do return .str (← stringLit? raw)
  | .paren _ e => eval p fuel env e
  | .unary _ op a => do unary op (← eval p fuel env a)
  -- `&&` and `||` evaluate the right operand only when the left one does
  -- not decide the result (Go specification, "Logical operators").
  | .binary _ op l r => do
    match BinOp.ofString? op with
    | some .land =>
      let .bool x ← eval p fuel env l | none
      if x then
        let .bool y ← eval p fuel env r | none
        return .bool y
      else return .bool false
    | some .lor =>
      let .bool x ← eval p fuel env l | none
      if x then return .bool true
      else
        let .bool y ← eval p fuel env r | none
        return .bool y
    | some o => binary o (← eval p fuel env l) (← eval p fuel env r)
    | none => none
  -- A call of a function of the package (Go specification, "Calls"): the
  -- arguments are evaluated in order, each parameter is a new variable
  -- bound to its argument, and the body runs. A variable of the same name
  -- would hide the function, and the subset has no function values.
  | .call _ (.ident _ f) args false => do
    if (env.lookup f).isSome then none
    let vs ← evalList p fuel env args
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let (params, body) ← p.funcs.lookup f
      if params.length != vs.length then none
      match ← execStmt p fuel (params.zip vs).reverse body with
      | .ret v => some v
      | .normal _ => none
  | _ => none
termination_by e => (fuel, sizeOf e, 0)

def evalList (p : Program) (fuel : Nat) (env : Env) : List Expr → Option (List Val)
  | [] => some []
  | e :: es => do return (← eval p fuel env e) :: (← evalList p fuel env es)
termination_by es => (fuel, sizeOf es, 0)

def execStmt (p : Program) (fuel : Nat) (env : Env) : Stmt → Option Outcome
  | .ret _ [e] => do return .ret (← eval p fuel env e)
  | .assign _ op [.ident _ x] [e] => do
    match AssignKind.ofString? op with
    -- `x := e` declares `x` in the innermost scope.
    | some .define => return .normal ((x, ← eval p fuel env e) :: env)
    -- `x = e` changes the innermost variable `x`.
    | some .assign =>
      let v ← eval p fuel env e
      let _ ← env.lookup x
      return .normal (env.set x v)
    | some (.compound o) =>
      let old ← env.lookup x
      return .normal (env.set x (← binary o old (← eval p fuel env e)))
    | none => none
  | .incDec _ op (.ident _ x) => do
    let o ← incDecOp? op
    let old ← env.lookup x
    return .normal (env.set x (← binary o old (.int 1)))
  -- `var x T = e` and `var x T` (Go specification, "Variable
  -- declarations"): without a value, `x` starts at the zero value of `T`.
  | .decl _ (.mk _ "var" [.value _ [x] (some type) values]) => do
    let v ← match values with
      | [e] => eval p fuel env e
      | [] => zeroOf p type
      | _ => none
    return .normal ((x, v) :: env)
  -- `if c { … } else …` (Go specification, "If statements"). Each branch is
  -- a block, so what it declares goes out of scope at its end.
  | .ifStmt _ none c t els => do
    let .bool b ← eval p fuel env c | none
    let out ← if b then execStmt p fuel env t
      else match els with
        | some f => execStmt p fuel env f
        | none => some (.normal env)
    match out with
    | .ret v => some (.ret v)
    | .normal env' => some (.normal (env'.drop (env'.length - env.length)))
  | .block _ body => do
    match ← exec p fuel env body with
    | .ret v => some (.ret v)
    | .normal env' => some (.normal (env'.drop (env'.length - env.length)))
  | _ => none
termination_by s => (fuel, sizeOf s, 0)

/-- Run statements in order, until one returns. -/
def exec (p : Program) (fuel : Nat) (env : Env) : List Stmt → Option Outcome
  | [] => some (.normal env)
  | s :: rest => do
    match ← execStmt p fuel env s with
    | .ret v => some (.ret v)
    | .normal env' => exec p fuel env' rest
termination_by ss => (fuel, sizeOf ss, 0)

end

/-- Call the function `name` of `p` with `args`, as a call expression
would. -/
def runIn (p : Program) (name : String) (args : List Val) (fuel : Nat := 64) : Option Val := do
  let (params, body) ← p.funcs.lookup name
  if params.length != args.length then none
  match ← execStmt p fuel (params.zip args).reverse body with
  | .ret v => some v
  | .normal _ => none

end tolean.Go.Eval
