import tolean.Prototype.LoopCore.Core
import tolean.Go.IR.Eval

namespace tolean.Prototype.LoopCore.Go

open tolean.Go

abbrev Result := Outcome Eval.Env Eval.Val

def outcome : Eval.Outcome → Result
  | .normal env => .normal env
  | .ret v => .ret v

/-- Go's current values have no slices. This separate, immutable parameter
store supplies them without changing the existing value or environment types. -/
abbrev Slices := String → Option (List Eval.Val)

def leave (outer inner : Eval.Env) : Option Eval.Env :=
  some (inner.drop (inner.length - outer.length))

/-- The extension uses real Go statements and delegates scalar operations.
Fuel bounds statement nesting, not the number of range iterations. -/
def run (p : Eval.Program) (slices : Slices) : Nat → Eval.Env → Syntax.Stmt → Option Result
  | 0, _, _ => none
  | fuel + 1, env, stmt =>
    match stmt with
    | .brk _ => some (.brk env)
    | .cont _ => some (.cont env)
    | .block _ stmts =>
      stmts.foldlM (fun out stmt =>
        match out with
        | .normal inner => run p slices fuel inner stmt
        | other => some other) (.normal env)
    | .ifStmt _ none c yes no => do
      let .bool b ← Eval.eval p fuel env c | none
      if b then run p slices fuel env yes
      else match no with | some no => run p slices fuel env no | none => some (.normal env)
    | .range _ (some ":=") (some (.ident _ "_")) (some (.ident _ x)) (.ident _ xs) body => do
      execLoop (fun inner => run p slices fuel inner body)
        (fun v outer => some ((x, v) :: outer)) leave env (← slices xs)
    | _ => (Eval.execStmt p fuel env stmt).map outcome

theorem range_head (p : Eval.Program) (slices : Slices) (fuel : Nat)
    (env : Eval.Env) (x xs : String) (body : Syntax.Stmt)
    (vs : List Eval.Val) (h : slices xs = some vs) :
    run p slices (fuel + 1) env
      (.range default (some ":=") (some (.ident default "_"))
        (some (.ident default x)) (.ident default xs) body) =
    execLoop (fun inner => run p slices fuel inner body)
      (fun v outer => some ((x, v) :: outer)) leave env vs := by
  simp [run, h]

/-- This is a conditional bridge, not a proof of a Go body translator.
The existing Go IR evaluator has no break or continue outcomes. -/
theorem fold_bridge (source : Eval.Env → Option Result)
    (target : Eval.Env → Option Result) (x : String)
    (step : ∀ env, target env = (source env).map Outcome.lower)
    (env : Eval.Env) (vs : List Eval.Val) :
    execLoop source (fun v outer => some ((x, v) :: outer)) leave env vs =
      runFold target (fun v outer => some ((x, v) :: outer)) leave env vs :=
  execLoop_eq_runFold source target _ leave step env vs

end tolean.Prototype.LoopCore.Go
