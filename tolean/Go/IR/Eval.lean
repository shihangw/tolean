import tolean.Go.IR
import tolean.Go.Spec.Eval
import tolean.Core.Loop

/-!
The meaning of the Tolean IR with the Go extension, as an evaluator over the
values of the interpreter in `Spec/Eval.lean`.

Each constructor of `IR.Expr` and `IR.Body` is one form of Lean code. The
evaluator gives it the value that the printed Lean computes, written as a Go
value: an `Int` is `Val.int`, a `Bool` is `Val.bool` and a `String` is
`Val.str`. A `Prop` such as `a < b` has the value of its `decide`.
`Int.tdiv` and `Int.tmod` are total, as in Lean: a zero divisor gives `0`
and the dividend. The translator tests the divisor before it divides, and
`throw` of the message gives the outcome `panic`, as `Except.error` does.
`f a >>= fun x => rest` runs a call of a function that can panic: the call's
panic ends the body, as `Except`'s bind does. A `let` adds a binding in front, as Lean's shadowing does, and `let (x, y) := …`
gives `x` and `y` their new values.

The evaluator gives a value only to the forms that the Go translator writes.
It gives none to the others, so no theorem says anything about them.

`translate_sound` in `Proof/Package.lean` proves one direction for every
function that the translator accepts: when this evaluator gives a value or a
panic for a call, the interpreter gives the same value or panic. So this file is trusted to mean
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
  | .pure, [a] => some a
  | _, _ => none

/-- The bindings that `let (x, y) := …` makes: each of `names`, with its value
in `inner`. A name that is bound already gets the new value in its place,
and a new name goes in front. -/
def bindState (names : List String) (inner outer : Env) : Option Env :=
  names.foldlM (fun ρ n => do
    let v ← inner.lookup n
    return if (ρ.lookup n).isSome then Eval.Env.set ρ n v else (n, v) :: ρ) outer

/-- Go's statement outcomes embed in the shared loop control type. A return
and a panic both end the loop, as `.ok` and `.error` of its return value. -/
def loopOutcome : Outcome → tolean.Core.Loop.Outcome Env (Except Val Val)
  | .normal env => .normal env
  | .ret value => .ret (.ok value)
  | .panic value => .ret (.error value)

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
      | _ => none
  | .intOp op a b => do
    let .int x ← Expr.eval fs fuel ρ a | none
    let .int y ← Expr.eval fs fuel ρ b | none
    return .int (op.apply x y)
  | .division op a b => do
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
  | .throw e => do return .panic (← Expr.eval fs fuel ρ e)
  | .state _ => some (.normal ρ)
  | .let name e rest => do Body.exec fs fuel ((name, ← Expr.eval fs fuel ρ e) :: ρ) rest
  | .ite c whenTrue whenFalse => do
    let .bool t ← Expr.eval fs fuel ρ c | none
    if t then Body.exec fs fuel ρ whenTrue else Body.exec fs fuel ρ whenFalse
  | .letState names branch rest => do
    match ← Body.exec fs fuel ρ branch with
    | .normal inner => Body.exec fs fuel (← bindState names inner ρ) rest
    | .panic x => some (.panic x)
    | .ret _ => none
  -- `f a b >>= fun x => rest`: the call's panic is the body's panic, and its
  -- value is bound to `x` otherwise.
  | .bind name ref args rest => do
    let vs ← Expr.evalList fs fuel ρ args
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let (params, body) ← fs.lookup ref
      if params.length != vs.length then none
      match ← Body.exec fs fuel (params.zip vs).reverse body with
      | .ret v => Body.exec fs (fuel + 1) ((name, v) :: ρ) rest
      | .panic x => some (.panic x)
      | .normal _ => none
  | .fold names element body (.list items _) rest _ => do
    let values ← Expr.evalList fs fuel ρ items
    let result ← tolean.Core.Loop.runFold
      (fun inner => (Body.exec fs fuel inner body).map loopOutcome)
      (fun value outer => some ((element, value) :: outer))
      (fun outer inner => bindState names inner outer) ρ values
    match result with
    | .normal inner => Body.exec fs fuel inner rest
    | .ret (.ok value) => some (.ret value)
    | .ret (.error value) => some (.panic value)
    | _ => none
  | _ => none
termination_by b => (fuel, sizeOf b, 0)

end

/-- Call the function `key` of the output with `args`: `.ok` of the value it
returns, or `.error` of the message it throws. -/
def runIn (fs : List (DeclRef × List String × Body)) (key : DeclRef) (args : List Val)
    (fuel : Nat := 64) : Option (Except Val Val) := do
  let (params, body) ← fs.lookup key
  if params.length != args.length then none
  match ← Body.exec fs fuel (params.zip args).reverse body with
  | .ret v => some (.ok v)
  | .panic x => some (.error x)
  | .normal _ => none

end tolean.Go.IR
