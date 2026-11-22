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

/-- The evaluator's language interface. Unsupported expressions fail explicitly. -/
structure Semantics (ρ v T E : Type) where
  expr : ρ → IR.Expr T E → Option v
  truth : v → Option Bool
  elements : v → Option (List v)
  put : String → v → ρ → ρ
  project : List String → ρ → ρ → Option ρ

/-- Meaning of the small shared IR fragment used here. -/
def evalIR (s : Semantics ρ v T E) (env : ρ) : IR.Body T E → Option (Outcome ρ v)
  | .value e | .exit e _ => return .ret (← s.expr env e)
  | .state _ | .yield _ _ => some (.normal env)
  | .done _ _ => some (.brk env)
  | .let n e rest => do evalIR s (s.put n (← s.expr env e) env) rest
  | .ite e yes no => do
    if ← s.truth (← s.expr env e) then evalIR s env yes else evalIR s env no
  | .fold ns binder body items rest _ => do
    let vs ← s.elements (← s.expr env items)
    match ← runFold (fun inner => evalIR s inner body)
        (fun x outer => some (s.put binder x outer)) (s.project ns) env vs with
    | .normal inner => evalIR s inner rest
    | .ret v => return .ret v
    | _ => none
  | _ => none

theorem lowerLoop_sound (s : Semantics ρ v T E)
    (changed : List (String × IR.Ty T)) (binder : String) (elem : IR.Ty T)
    (source : ρ → Option (Outcome ρ v)) (body rest : IR.Body T E)
    (items : IR.Expr T E) (breaks : Bool) (returns : Option (IR.Ty T))
    (step : ∀ env, evalIR s env body = (source env).map Outcome.lower)
    (env : ρ) (vs : List v)
    (head : (s.expr env items >>= s.elements) = some vs) :
    evalIR s env (lowerLoop changed binder elem body items rest breaks returns) =
      (do
        match ← execLoop source (fun x outer => some (s.put binder x outer))
            (s.project (changed.map Prod.fst)) env vs with
        | .normal inner => evalIR s inner rest
        | .ret v => return .ret v
        | _ => none) := by
  simp only [lowerLoop, evalIR]
  rw [execLoop_eq_runFold source _ _ _ step]
  cases he : s.expr env items <;> simp_all

end tolean.Prototype.LoopCore
