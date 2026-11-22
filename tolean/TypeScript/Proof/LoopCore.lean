import tolean.Core.Loop
import tolean.TypeScript.Proof.LoopHead

namespace tolean.TypeScript.Proof.LoopCore

open tolean.Core.Loop
open tolean.TypeScript

variable {N : Type} [JSNumber N]

def outcome : Eval.Outcome N → Outcome (Eval.Env N) (Except (Eval.Val N) (Eval.Val N))
  | .normal env => .normal env
  | .ret value => .ret value
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

theorem runFold_eq (fs : List (DeclRef × List String × IR.Body))
    (fuel : Nat) (names : List String) (element : String) (body : IR.Body)
    (env : Eval.Env N) (vs : List (Eval.Val N)) :
    (IR.Body.runFold fs fuel names element body env vs).map outcome =
      runFold (fun inner => (IR.Body.exec fs fuel inner body).map outcome)
        (fun x outer => some ((element, x) :: outer))
        (fun outer inner => IR.bindState names inner outer) env vs := by
  induction vs generalizing env with
  | nil => simp [IR.Body.runFold, runFold, outcome]
  | cons x xs ih =>
    simp only [IR.Body.runFold, runFold]
    simp
    cases hs : IR.Body.exec fs fuel ((element, x) :: env) body with
    | none => rfl
    | some o =>
      cases o <;> simp [outcome]
      all_goals
        cases IR.bindState names _ env <;> simp
      all_goals first | exact ih _ | rfl

theorem execCounted_eq (m : Eval.Scope) (fuel : Nat) (body : Syntax.Stmt)
    (name : String) (bound : N) (start : Int) (left : Nat)
    (env : Eval.Env N) (values : List N)
    (head : JSNumber.countFrom bound [] start left = some values) :
    (Eval.execCounted m fuel env name body bound start left).map outcome =
      execLoop (fun inner => (Eval.execStmt m fuel inner body).map outcome)
        (fun x outer => some ((name, x) :: outer))
        (fun outer inner => some (inner.drop (inner.length - outer.length)))
        env (values.map Eval.Val.num) := by
  rw [tolean.TypeScript.Proof.execCounted_eq m fuel env values head]
  exact execLoop_eq m fuel body (fun v => some [(name, v)]) env _

end tolean.TypeScript.Proof.LoopCore
