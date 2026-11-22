import tolean.IR

namespace tolean.Prototype.LoopCore

inductive Outcome (ρ v : Type) where
  | normal (env : ρ)
  | ret (value : v)
  | brk (env : ρ)
  | cont (env : ρ)
deriving Repr, DecidableEq

def Outcome.lower : Outcome ρ v → Outcome ρ v
  | .cont s => .normal s
  | o => o

def execLoop (body : ρ → Option (Outcome ρ r))
    (bind : v → ρ → Option ρ) (leave : ρ → ρ → Option ρ)
    (env : ρ) : List v → Option (Outcome ρ r)
  | [] => some (.normal env)
  | x :: xs => do
    match ← body (← bind x env) with
    | .ret v => return .ret v
    | .normal inner | .cont inner => execLoop body bind leave (← leave env inner) xs
    | .brk inner => return .normal (← leave env inner)

/-- The IR rejects an unlowered continue. A translated continue yields state. -/
def runFold (body : ρ → Option (Outcome ρ r))
    (bind : v → ρ → Option ρ) (leave : ρ → ρ → Option ρ)
    (env : ρ) : List v → Option (Outcome ρ r)
  | [] => some (.normal env)
  | x :: xs => do
    match ← body (← bind x env) with
    | .ret v => return .ret v
    | .normal inner => runFold body bind leave (← leave env inner) xs
    | .brk inner => return .normal (← leave env inner)
    | .cont _ => none

/-- One-iteration agreement includes failure and all four control outcomes.
The two runners share a state representation, but that representation is arbitrary. -/
theorem execLoop_eq_runFold
    (source target : ρ → Option (Outcome ρ r))
    (bind : v → ρ → Option ρ) (leave : ρ → ρ → Option ρ)
    (step : ∀ s, target s = (source s).map Outcome.lower)
    (env : ρ) (items : List v) :
    execLoop source bind leave env items = runFold target bind leave env items := by
  induction items generalizing env with
  | nil => rfl
  | cons x xs ih =>
    simp only [execLoop, runFold]
    cases hb : bind x env with
    | none => rfl
    | some s =>
      simp [step]
      cases hs : source s with
      | none => rfl
      | some o =>
        cases o <;> simp [Outcome.lower]
        all_goals first
          | rfl
          | (cases leave env _ <;> simp_all)

def lowerLoop (changed : List (String × IR.Ty T)) (binder : String)
    (elem : IR.Ty T) (body : IR.Body T E) (items : IR.Expr T E)
    (rest : IR.Body T E) (breaks : Bool) (returns : Option (IR.Ty T))
    (scope : List (String × IR.Ty T) := []) : IR.Body T E :=
  .fold (changed.map Prod.fst) binder body items rest
    { span := default, stateTypes := changed.map Prod.snd, elem, scope,
      breaks := breaks || returns.isSome, returns }

end tolean.Prototype.LoopCore
