import tolean.TypeScript.Syntax.Ast

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
The subset has no `number` yet: `number` values come in a later phase.
-/
namespace tolean.TypeScript.Eval

open tolean.TypeScript.Syntax

/-- A span, written short in certificates. -/
abbrev sp (a b c d : Nat) : tolean.Span := ⟨⟨a, b⟩, ⟨c, d⟩⟩

/-- A JavaScript value of the subset. An object is a list of fields, in the
order the program wrote them. -/
inductive Val where
  | int (i : Int)
  | bool (b : Bool)
  | str (s : String)
  | null
  | list (items : List Val)
  | obj (fields : List (String × Val))
deriving Repr, Inhabited, BEq

/-- `ToBoolean` (ECMA-262 §7.1.2), on the values of the subset. -/
def Val.truthy : Val → Bool
  | .int i => i != 0
  | .bool b => b
  | .str s => !s.isEmpty
  | .null => false
  | .list _ | .obj _ => true

/-- The variables in scope, innermost first. -/
abbrev Env := List (String × Val)

/-- Change the innermost variable named `name`. -/
def Env.set (env : Env) (name : String) (v : Val) : Env :=
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

/-- `IsStrictlyEqual` (ECMA-262 §7.2.15) on primitive values, and between
`null` and any value. Values of different types are not equal, so `null` is
never equal to an object. Two objects compare by identity, which the subset
does not model, so they leave it. -/
def strictEq : Val → Val → Option Bool
  | .int a, .int b => some (decide (a = b))
  | .bool a, .bool b => some (decide (a = b))
  | .str a, .str b => some (decide (a = b))
  | .null, .null => some true
  | .null, .int _ | .null, .bool _ | .null, .str _ | .null, .list _ | .null, .obj _ => some false
  | .int _, .null | .bool _, .null | .str _, .null | .list _, .null | .obj _, .null => some false
  | _, _ => none

/-- A binary operator on two values, when neither operand short-circuits.
Bigint `/` and `%` truncate toward zero and throw on a zero divisor
(`BigInt::divide`, `BigInt::remainder`). -/
def binary : BinOp → Val → Val → Option Val
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .div, .int a, .int b => if b == 0 then none else some (.int (a.tdiv b))
  | .mod, .int a, .int b => if b == 0 then none else some (.int (a.tmod b))
  | .lt, .int a, .int b => some (.bool (decide (a < b)))
  | .gt, .int a, .int b => some (.bool (decide (a > b)))
  | .le, .int a, .int b => some (.bool (decide (a ≤ b)))
  | .ge, .int a, .int b => some (.bool (decide (a ≥ b)))
  | .strictEq, a, b => (strictEq a b).map .bool
  | .strictNe, a, b => (strictEq a b).map (.bool ∘ not)
  | _, _, _ => none

/-- What a statement list does: it runs to its end with the variables it
leaves, or it returns a value. -/
inductive Outcome where
  | normal (env : Env)
  | ret (v : Val)
deriving Inhabited

/-- The functions of the module, by name. -/
def functions (m : Module) : List (String × List String × Stmt) :=
  m.decls.filterMap fun
    | .function _ _ name params _ body => some (name, params.map (·.name), body)
    | _ => none

mutual

/-- The value of `e`. `fuel` bounds the depth of nested calls, so that the
interpreter is a total function. -/
def eval (m : Module) (fuel : Nat) (env : Env) : Expr → Option Val
  | .ident _ name => env.lookup name
  | .bigint _ text => (bigintLiteral text).map .int
  | .bool _ b => some (.bool b)
  | .string _ s => some (.str s)
  | .null _ => some .null
  | .paren _ inner => eval m fuel env inner
  | .array _ elems => (evalList m fuel env elems).map .list
  | .object _ props => (evalProps m fuel env props).map .obj
  | .member _ obj name => do
    match ← eval m fuel env obj with
    | .obj fields => fields.lookup name
    | _ => none
  | .unary _ .not arg => do return .bool !(← eval m fuel env arg).truthy
  | .unary _ .neg arg => do
    match ← eval m fuel env arg with
    | .int i => some (.int (-i))
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
    if a == .null then eval m fuel env r else some a
  | .binary _ op l r => do binary op (← eval m fuel env l) (← eval m fuel env r)
  | .cond _ test t f => do
    if (← eval m fuel env test).truthy then eval m fuel env t else eval m fuel env f
  | .call _ (.ident _ name) args => do
    let vs ← evalList m fuel env args
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let (params, body) ← (functions m).lookup name
      if params.length != vs.length then none
      match ← execStmt m fuel (params.zip vs).reverse body with
      | .ret v => some v
      | .normal _ => none
  | _ => none
termination_by e => (fuel, sizeOf e, 0)

def evalList (m : Module) (fuel : Nat) (env : Env) : List Expr → Option (List Val)
  | [] => some []
  | e :: es => do return (← eval m fuel env e) :: (← evalList m fuel env es)
termination_by es => (fuel, sizeOf es, 0)

def evalProps (m : Module) (fuel : Nat) (env : Env) : List Property → Option (List (String × Val))
  | [] => some []
  | .shorthand _ name :: ps => do return (name, ← env.lookup name) :: (← evalProps m fuel env ps)
  | .keyValue _ (.ident key) v :: ps => do
    return (key, ← eval m fuel env v) :: (← evalProps m fuel env ps)
  | _ :: _ => none
termination_by ps => (fuel, sizeOf ps, 0)

/-- Run one statement. A block, and the branch of an `if`, keep the changes
they make to outer variables and drop the variables they declare. -/
def execStmt (m : Module) (fuel : Nat) (env : Env) : Stmt → Option Outcome
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
  | .block _ body => do
    match ← exec m fuel env body with
    | .ret v => some (.ret v)
    | .normal env' => some (.normal (env'.drop (env'.length - env.length)))
  | .empty _ => some (.normal env)
  -- `for (const x of xs)` on an array: the body runs once for each element,
  -- in order, with `x` bound to it in a new scope (`ForIn/OfBodyEvaluation`,
  -- ECMA-262 §14.7.5.7, with the array iterator of §23.1.5.1).
  | .forOfStmt _ .const name iterable body => do
    let .list items ← eval m fuel env iterable | none
    execLoop m fuel env name body items
  | _ => none
termination_by s => (fuel, sizeOf s, 0)

/-- Run the body of `for (const name of …)` once for each of `items`. Each
run keeps the changes to outer variables, and drops `name` and the variables
the body declares. -/
def execLoop (m : Module) (fuel : Nat) (env : Env) (name : String) (body : Stmt) :
    List Val → Option Outcome
  | [] => some (.normal env)
  | x :: xs => do
    match ← execStmt m fuel ((name, x) :: env) body with
    | .ret v => some (.ret v)
    | .normal env' => execLoop m fuel (env'.drop (env'.length - env.length)) name body xs
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- Run a statement list, up to its end or its first `return`. -/
def exec (m : Module) (fuel : Nat) (env : Env) : List Stmt → Option Outcome
  | [] => some (.normal env)
  | s :: rest => do
    match ← execStmt m fuel env s with
    | .ret v => some (.ret v)
    | .normal env' => exec m fuel env' rest
termination_by ss => (fuel, sizeOf ss, 0)

end

/-- Call the function `name` of `m` with `args`, as a call expression would
(ECMA-262 §10.2.1): bind each parameter to its argument, run the body, and
take the value it returns. -/
def run (m : Module) (name : String) (args : List Val) (fuel : Nat := 64) : Option Val := do
  let (params, body) ← (functions m).lookup name
  if params.length != args.length then none
  match ← execStmt m fuel (params.zip args).reverse body with
  | .ret v => some v
  | .normal _ => none

end tolean.TypeScript.Eval

namespace tolean.TypeScript.Eval

/-- The proof of a certificate theorem: unfold the interpreter on the program
and the translated definitions, then split on each branch. `defs` names the
program, the encoders and the translated functions. -/
syntax "certify_tac" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| certify_tac [$defs,*]) =>
    `(tactic| (
      simp [run, eval, evalList, evalProps, execStmt, exec, execLoop, functions, binary, strictEq,
        bigintLiteral, digitsIn, digitIn, Env.set, Val.truthy, List.lookup, $defs,*]
      all_goals repeat' (split <;> (try simp_all [List.lookup, binary, strictEq, Val.truthy, Env.set, $defs,*]))
      all_goals (try simp_all [List.lookup, binary, strictEq, Val.truthy, Env.set, $defs,*])))

end tolean.TypeScript.Eval
