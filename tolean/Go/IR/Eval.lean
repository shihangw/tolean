import tolean.Go.IR
import tolean.Go.Spec.Eval

/-!
The meaning of the Tolean IR with the Go extension, as an evaluator over the
values of the interpreter in `Spec/Eval.lean`.

Each constructor of `IR.Expr` and `IR.Body` is one form of Lean code. The
evaluator gives it the value that the printed Lean computes, written as a Go
value: an `Int` is `Val.int`, a `Bool` is `Val.bool` and a `String` is
`Val.str`. A `Prop` such as `a < b` has the value of its `decide`. A `let`
adds a binding in front, as Lean's shadowing does, and `let (x, y) := …`
gives `x` and `y` their new values.

The evaluator gives a value only to the forms that the Go translator writes.
It gives none to the others, so no theorem says anything about them.

`translate_sound` in `Proof/Package.lean` proves one direction for every
function that the translator accepts: when this evaluator gives a value for a
call, the interpreter gives the same value. So this file is trusted to mean
what the printed Lean means, and to give a value where the printed Lean does.
-/
namespace tolean.Go.IR

open tolean.Go.Eval (Val Env Outcome)

/-- The functions of the output, by name: their parameters and their body. -/
def functions (decls : List Decl) : List (DeclRef × List String × Body) :=
  decls.filterMap fun
    | .function name params _ body => some (⟨"", name⟩, params.map (·.1), body)
    | _ => none

/-- An operation that Go adds, on the values of its arguments. -/
def ExprExt.apply : ExprExt → List Val → Option Val
  | .wrap64, [.int a] => some (.int (tolean.Go.wrap64 a))
  | .append, [.str a, .str b] => some (.str (a ++ b))
  | _, _ => none

/-- The bindings that `let (x, y) := …` makes: each of `names`, with its value
in `inner`. A name that is bound already gets the new value in its place,
and a new name goes in front. -/
def bindState (names : List String) (inner outer : Env) : Option Env :=
  names.foldlM (fun ρ n => do
    let v ← inner.lookup n
    return if (ρ.lookup n).isSome then Eval.Env.set ρ n v else (n, v) :: ρ) outer

mutual

/-- The value of `e`. `fuel` bounds the depth of nested calls. -/
def Expr.eval (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env) :
    Expr → Option Val
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | .string s => some (.str s)
  | .var name => ρ.lookup name
  | .not p => do
    let .bool b ← Expr.eval fs fuel ρ p | none
    return .bool !b
  | .neg a => do
    let .int i ← Expr.eval fs fuel ρ a | none
    return .int (-i)
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
  | .intOp op a b => do
    let .int x ← Expr.eval fs fuel ρ a | none
    let .int y ← Expr.eval fs fuel ρ b | none
    return .int (op.apply x y)
  | .order op a b => do
    let .int x ← Expr.eval fs fuel ρ a | none
    let .int y ← Expr.eval fs fuel ρ b | none
    return .bool (op.apply x y)
  | .eq a b => do
    return .bool (← Eval.eqVal (← Expr.eval fs fuel ρ a) (← Expr.eval fs fuel ρ b))
  | .ne a b => do
    return .bool !(← Eval.eqVal (← Expr.eval fs fuel ρ a) (← Expr.eval fs fuel ρ b))
  | .and p q => do
    let .bool x ← Expr.eval fs fuel ρ p | none
    let .bool y ← Expr.eval fs fuel ρ q | none
    return .bool (x && y)
  | .or p q => do
    let .bool x ← Expr.eval fs fuel ρ p | none
    let .bool y ← Expr.eval fs fuel ρ q | none
    return .bool (x || y)
  | .decide p => Expr.eval fs fuel ρ p
  | .ext op args => do op.apply (← Expr.evalList fs fuel ρ args)
  | _ => none
termination_by e => (fuel, sizeOf e, 0)

def Expr.evalList (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env) :
    List Expr → Option (List Val)
  | [] => some []
  | e :: es => do return (← Expr.eval fs fuel ρ e) :: (← Expr.evalList fs fuel ρ es)
termination_by es => (fuel, sizeOf es, 0)

/-- Run a body: it returns the function's value, or it ends in the state of a
branch, with the bindings it has made. -/
def Body.exec (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env) :
    Body → Option Outcome
  | .value e => do return .ret (← Expr.eval fs fuel ρ e)
  | .state _ => some (.normal ρ)
  | .let name e rest => do Body.exec fs fuel ((name, ← Expr.eval fs fuel ρ e) :: ρ) rest
  | .ite c whenTrue whenFalse => do
    let .bool t ← Expr.eval fs fuel ρ c | none
    if t then Body.exec fs fuel ρ whenTrue else Body.exec fs fuel ρ whenFalse
  | .letState names branch rest => do
    match ← Body.exec fs fuel ρ branch with
    | .normal inner => Body.exec fs fuel (← bindState names inner ρ) rest
    | .ret _ => none
  | _ => none
termination_by b => (fuel, sizeOf b, 0)

end

/-- Call the function `key` of the output with `args`. -/
def runIn (fs : List (DeclRef × List String × Body)) (key : DeclRef) (args : List Val)
    (fuel : Nat := 64) : Option Val := do
  let (params, body) ← fs.lookup key
  if params.length != args.length then none
  match ← Body.exec fs fuel (params.zip args).reverse body with
  | .ret v => some v
  | .normal _ => none

end tolean.Go.IR
