namespace tolean.Runtime

/-- The shared result of a loop that can return from its function. -/
inductive LoopResult (R σ : Type) where
  | returned (value : R)
  | completed (state : σ)

namespace LoopResult

/-- Turn a return slot and the final loop state into the shared carrier. -/
def ofParts {R σ : Type} (returned : Option R) (state : σ) : LoopResult R σ :=
  match returned with
  | some value => .returned value
  | none => .completed state

/-- Run the continuation selected by a loop result. -/
def run {R σ α : Type} (result : LoopResult R σ) (onReturn : R → α) (onComplete : σ → α) : α :=
  match result with
  | .returned value => onReturn value
  | .completed state => onComplete state

/-- Select the return or continuation arm of a loop with no changed locals. -/
def runOption {R α : Type} (result : Option R) (onReturn : R → α) (onComplete : Unit → α) : α :=
  run (ofParts result ()) onReturn onComplete

/-- Select the return or continuation arm of a loop with changed locals. -/
def runPair {R σ α : Type} (result : Option R × σ) (onReturn : R → α) (onComplete : σ → α) : α :=
  run (ofParts result.1 result.2) onReturn onComplete

end LoopResult
end tolean.Runtime
