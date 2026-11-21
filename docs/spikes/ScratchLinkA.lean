import tolean.TypeScript.Proof.Link

open tolean.TypeScript tolean.TypeScript.Eval

namespace tolean.TypeScript.Proof

variable {N : Type} [JSNumber N]

theorem bodyExec_fold_loopResult
    (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (names : List String) (element : String) (body : IR.Body)
    (items : IR.Expr) (rest : IR.Body)
    (info : tolean.IR.LoopInfo tolean.TypeScript.IR.TyExt)
    (ρ : Env N) (vs : List (Val N))
    (result : tolean.IR.LoopResult (Except (Val N) (Val N)) (Env N))
    (hitems : IR.Expr.eval fs fuel ρ items = some (.list vs))
    (hfold : IR.Body.runFold fs fuel names element body ρ vs =
      some (match result with
        | .returned value => .ret value
        | .completed state => .normal state)) :
    IR.Body.exec fs fuel ρ (.fold names element body items rest info) =
      tolean.IR.LoopResult.run result
        (fun value => some (Outcome.ret value))
        (fun state => IR.Body.exec fs fuel state rest) := by
  cases result with
  | returned value => simp [IR.Body.exec, hitems, hfold, tolean.IR.LoopResult.run]
  | completed state => simp [IR.Body.exec, hitems, hfold, tolean.IR.LoopResult.run]

end tolean.TypeScript.Proof
