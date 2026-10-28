import tolean.TypeScript.Output
import tolean.TypeScript.Spec.Eval

/-!
The meaning of the translator's output tree, as an evaluator over the values
of the interpreter in `Spec/Eval.lean`.

Each constructor of `Output.Expr` and `Output.Body` is one form of Lean code.
The evaluator gives it the value that the printed Lean computes, written as a
JavaScript value: an `Int` is `Val.int`, `none` is `Val.null`, `some v` is the
value of `v`, a list is `Val.list`, and a structure is `Val.obj` with its
fields in the declared order. A `let` adds a binding in front, as Lean's
shadowing does.

`translate_sound` in `Proof/Module.lean` proves one direction for every
program that the translator accepts: when this evaluator gives a value for a
call, the interpreter gives the same value. So this file is trusted to mean
what the printed Lean means, and to give a value where the printed Lean does.
Step 4 of phase 6 of the certificates plan would check that for each file.
-/
namespace tolean.TypeScript.Output

open tolean.TypeScript.Eval (Val Env Outcome)

variable {N : Type} [JSNumber N]

/-- The functions of the output of `file`, by name: their parameters and their
body. -/
def functions (decls : List Decl) : List (String × List String × Body) :=
  decls.filterMap fun
    | .function name params _ body => some (name, params.map (·.1), body)
    | .struct .. => none

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

def IntOp.apply : IntOp → Int → Int → Int
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·)

def Order.apply : Order → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)

def Division.apply : Division → Int → Int → Int
  | .tdiv => Int.tdiv | .tmod => Int.tmod

def NumberOp.apply : NumberOp → N → N → Val N
  | .add, a, b => .num (JSNumber.add a b)
  | .sub, a, b => .num (JSNumber.sub a b)
  | .mul, a, b => .num (JSNumber.mul a b)
  | .lt, a, b => .bool (JSNumber.lt a b)
  | .le, a, b => .bool (JSNumber.le a b)
  | .eq, a, b => .bool (JSNumber.eq a b)

def NumberConstant.value : NumberConstant → N
  | .nan => JSNumber.nan | .posInf => JSNumber.posInf | .negInf => JSNumber.negInf

def NumberTest.apply : NumberTest → N → Bool
  | .isSafeInteger, a => (JSNumber.toSafeInt a).isSome
  | .isNaN, a => JSNumber.isNaN a
  | .isFinite, a => JSNumber.isFinite a

/-- The bindings that `let (x, y) := …` adds: each of `names`, with its value
in `inner`. -/
def bindState (names : List String) (inner outer : Env N) : Option (Env N) :=
  names.foldlM (fun ρ n => do return (n, ← inner.lookup n) :: ρ) outer

mutual

/-- The value of `e`. `fuel` bounds the depth of nested calls. -/
def Expr.eval (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N) :
    Expr → Option (Val N)
  | .int n => some (.int n)
  | .number n => some (.num (JSNumber.ofSafeInt n))
  | .numberConstant c => some (.num c.value)
  | .none => some .null
  | .bool b => some (.bool b)
  | .string s => some (.str s)
  | .var name => ρ.lookup name
  | .field obj _ name => do
    match ← Expr.eval fs fuel ρ obj with
    | .obj fields => fields.lookup name
    | _ => none
  | .propNot p | .not p => do
    let .bool b ← Expr.eval fs fuel ρ p | none
    return .bool !b
  | .neg a => do
    let .int i ← Expr.eval fs fuel ρ a | none
    return .int (-i)
  | .numberNeg a => do
    let .num n ← Expr.eval fs fuel ρ a | none
    return .num (JSNumber.neg n)
  | .ite c a b => do
    let .bool t ← Expr.eval fs fuel ρ c | none
    if t then Expr.eval fs fuel ρ a else Expr.eval fs fuel ρ b
  | .call ref args => do
    let vs ← Expr.evalList fs fuel ρ args
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let (params, body) ← fs.lookup ref
      if params.length != vs.length then none
      match ← Body.exec fs fuel (params.zip vs).reverse body with
      | .ret v => some v
      | .normal _ => none
  | .list elems _ => do return .list (← Expr.evalList fs fuel ρ elems)
  | .struct fields _ => do return .obj (← Expr.evalFields fs fuel ρ fields)
  | .isNone a => do
    match ← Expr.eval fs fuel ρ a with
    | .null => return .bool true
    | _ => return .bool false
  | .isSome a => do
    match ← Expr.eval fs fuel ρ a with
    | .null => return .bool false
    | _ => return .bool true
  | .matchNull name whenNull whenValue => do
    match ← ρ.lookup name with
    | .null => Expr.eval fs fuel ρ whenNull
    | _ => Expr.eval fs fuel ρ whenValue
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
  | .numberOp op a b => do
    let .num x ← Expr.eval fs fuel ρ a | none
    let .num y ← Expr.eval fs fuel ρ b | none
    return op.apply x y
  | .numberNe a b => do
    let .num x ← Expr.eval fs fuel ρ a | none
    let .num y ← Expr.eval fs fuel ρ b | none
    return .bool !(JSNumber.eq x y)
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
  | .numberTest test a => do
    let .num n ← Expr.eval fs fuel ρ a | none
    return .bool (test.apply n)
  | .push name a => do
    let .list xs ← ρ.lookup name | none
    return .list (xs ++ [← Expr.eval fs fuel ρ a])
  | .update op name a => do
    let .int x ← ρ.lookup name | none
    let .int y ← Expr.eval fs fuel ρ a | none
    return .int (op.apply x y)
termination_by e => (fuel, sizeOf e, 0)

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
  | .value e => do return .ret (← Expr.eval fs fuel ρ e)
  | .state _ => some (.normal ρ)
  | .let name e rest => do Body.exec fs fuel ((name, ← Expr.eval fs fuel ρ e) :: ρ) rest
  | .letArray name _ elems rest => do
    Body.exec fs fuel ((name, .list (← Expr.evalList fs fuel ρ elems)) :: ρ) rest
  | .ite c whenTrue whenFalse => do
    let .bool t ← Expr.eval fs fuel ρ c | none
    if t then Body.exec fs fuel ρ whenTrue else Body.exec fs fuel ρ whenFalse
  | .matchNull name whenNull whenValue => do
    match ← ρ.lookup name with
    | .null => Body.exec fs fuel ρ whenNull
    | _ => Body.exec fs fuel ρ whenValue
  | .letState names branch rest => do
    match ← Body.exec fs fuel ρ branch with
    | .normal inner => Body.exec fs fuel (← bindState names inner ρ) rest
    | .ret _ => none
  | .fold names element body items rest _ => do
    let .list vs ← Expr.eval fs fuel ρ items | none
    Body.exec fs fuel (← Body.runFold fs fuel names element body ρ vs) rest
termination_by b => (fuel, sizeOf b, 0)

/-- `List.foldl` over `items` with the step `fun (names) element => body`: the
bindings of `names` after each element, on top of `ρ`. -/
def Body.runFold (fs : List (DeclRef × List String × Body)) (fuel : Nat) (names : List String)
    (element : String) (body : Body) (ρ : Env N) : List (Val N) → Option (Env N)
  | [] => some ρ
  | x :: xs => do
    match ← Body.exec fs fuel ((element, x) :: ρ) body with
    | .normal inner => Body.runFold fs fuel names element body (← bindState names inner ρ) xs
    | .ret _ => none
termination_by xs => (fuel, sizeOf body, xs.length + 1)

end

/-- Call the function `key` of the output with `args`. -/
def runIn (fs : List (DeclRef × List String × Body)) (key : DeclRef) (args : List (Val N))
    (fuel : Nat := 64) : Option (Val N) := do
  let (params, body) ← fs.lookup key
  if params.length != args.length then none
  match ← Body.exec fs fuel (params.zip args).reverse body with
  | Outcome.ret v => some v
  | Outcome.normal _ => none

end tolean.TypeScript.Output
