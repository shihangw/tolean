import tolean.Prototype.LoopCore.Core
import tolean.TypeScript.IR.Eval

namespace tolean.Prototype.LoopCore.TypeScript

open tolean.TypeScript

variable {N : Type} [JSNumber N]

def outcome : Eval.Outcome N → Outcome (Eval.Env N) (Except (Eval.Val N) (Eval.Val N))
  | .normal env => .normal env
  | .ret v => .ret v
  | .brk env => .brk env
  | .cont env => .cont env

theorem execLoop_eq (m : Eval.Scope) (fuel : Nat) (body : Syntax.Stmt)
    (bind : Eval.Val N → Option (Eval.Env N)) (env : Eval.Env N) (vs : List (Eval.Val N)) :
    (Eval.execLoop m fuel env bind body vs).map outcome =
      execLoop (fun inner => (Eval.execStmt m fuel inner body).map outcome)
        (fun x outer => (bind x).map (· ++ outer))
        (fun outer inner => some (inner.drop (inner.length - outer.length))) env vs := by
  induction vs generalizing env with
  | nil => simp [Eval.execLoop, execLoop, outcome]
  | cons x xs ih =>
    simp only [Eval.execLoop, execLoop]
    cases hb : bind x with
    | none => rfl
    | some locals =>
      simp
      cases hs : Eval.execStmt m fuel (locals ++ env) body with
      | none => rfl
      | some o =>
        cases o <;> simp [outcome]
        all_goals exact ih _

theorem runFold_eq (fs : List (DeclRef × List String × tolean.TypeScript.IR.Body))
    (fuel : Nat) (names : List String) (element : String) (body : tolean.TypeScript.IR.Body)
    (env : Eval.Env N) (vs : List (Eval.Val N)) :
    (tolean.TypeScript.IR.Body.runFold fs fuel names element body env vs).map outcome =
      runFold (fun inner => (tolean.TypeScript.IR.Body.exec fs fuel inner body).map outcome)
        (fun x outer => some ((element, x) :: outer))
        (fun outer inner => tolean.TypeScript.IR.bindState names inner outer) env vs := by
  induction vs generalizing env with
  | nil => simp [tolean.TypeScript.IR.Body.runFold, runFold, outcome]
  | cons x xs ih =>
    simp only [tolean.TypeScript.IR.Body.runFold, runFold]
    simp
    cases hs : tolean.TypeScript.IR.Body.exec fs fuel ((element, x) :: env) body with
    | none => rfl
    | some o =>
      cases o <;> simp [outcome]
      all_goals
        cases tolean.TypeScript.IR.bindState names _ env <;> simp
      all_goals first | exact ih _ | rfl

end tolean.Prototype.LoopCore.TypeScript
