import tolean.IR

namespace tolean.Core.Loop

inductive Outcome (ρ v : Type) where
  | normal (env : ρ)
  | ret (value : v)
  | brk (env : ρ)
  | cont (env : ρ)
deriving Repr, DecidableEq

def Outcome.lower : Outcome ρ v → Outcome ρ v
  | .cont s => .normal s
  | o => o

/-- Stores and return values may have different representations on each side. -/
def Outcome.Rel (R : ρ → σ → Prop) (V : r → q → Prop) :
    Outcome ρ r → Outcome σ q → Prop
  | .normal s, .normal t | .brk s, .brk t | .cont s, .cont t => R s t
  | .ret a, .ret b => V a b
  | _, _ => False

/-- Failure is related only to failure. This is an exact simulation, not a
claim that an undefined source execution can justify arbitrary target code. -/
def Related (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem Related.bind {R : α → β → Prop} {S : γ → δ → Prop}
    {a : Option α} {b : Option β} (h : Related R a b)
    (f : α → Option γ) (g : β → Option δ)
    (step : ∀ a b, R a b → Related S (f a) (g b)) :
    Related S (a >>= f) (b >>= g) := by
  cases a <;> cases b <;> simp_all [Related]

def execLoop (body : ρ → Option (Outcome ρ r))
    (bind : v → ρ → Option ρ) (leave : ρ → ρ → Option ρ)
    (env : ρ) : List v → Option (Outcome ρ r)
  | [] => some (.normal env)
  | x :: xs => do
    match ← body (← bind x env) with
    | .ret v => return .ret v
    | .normal inner | .cont inner => execLoop body bind leave (← leave env inner) xs
    | .brk inner => return .normal (← leave env inner)

/-- A translated continue yields state. An unlowered IR continue is rejected. -/
def runFold (body : σ → Option (Outcome σ q))
    (bind : v → σ → Option σ) (leave : σ → σ → Option σ)
    (env : σ) : List v → Option (Outcome σ q)
  | [] => some (.normal env)
  | x :: xs => do
    match ← body (← bind x env) with
    | .ret v => return .ret v
    | .normal inner => runFold body bind leave (← leave env inner) xs
    | .brk inner => return .normal (← leave env inner)
    | .cont _ => none

/-- The loop induction needs laws for both binding and leaving a scope.
In particular, agreement before scope exit does not by itself imply agreement
after scope exit. Languages must prove the latter law for their store relation. -/
theorem execLoop_sim
    (R : ρ → σ → Prop) (V : r → q → Prop)
    (source : ρ → Option (Outcome ρ r)) (target : σ → Option (Outcome σ q))
    (bindS : v → ρ → Option ρ) (bindT : v → σ → Option σ)
    (leaveS : ρ → ρ → Option ρ) (leaveT : σ → σ → Option σ)
    (bindLaw : ∀ x s t, R s t → Related R (bindS x s) (bindT x t))
    (leaveLaw : ∀ s t si ti, R s t → R si ti →
      Related R (leaveS s si) (leaveT t ti))
    (bodyLaw : ∀ s t, R s t →
      Related (fun a b => Outcome.Rel R V a.lower b) (source s) (target t))
    (s : ρ) (t : σ) (initial : R s t) (items : List v) :
    Related (Outcome.Rel R V)
      (execLoop source bindS leaveS s items) (runFold target bindT leaveT t items) := by
  induction items generalizing s t with
  | nil => exact initial
  | cons x xs ih =>
    simp only [execLoop, runFold]
    apply Related.bind (bindLaw x s t initial)
    intro si ti bound
    apply Related.bind (bodyLaw si ti bound)
    intro a b step
    cases a <;> cases b <;> simp only [Outcome.lower, Outcome.Rel] at step
    all_goals try contradiction
    · apply Related.bind (leaveLaw s t _ _ initial step)
      intro sn tn next
      exact ih sn tn next
    · exact step
    · apply Related.bind (leaveLaw s t _ _ initial step)
      intro sn tn next
      exact next
    · apply Related.bind (leaveLaw s t _ _ initial step)
      intro sn tn next
      exact ih sn tn next

theorem Related.eq_iff (a b : Option α) : Related Eq a b ↔ a = b := by
  cases a <;> cases b <;> simp [Related]

theorem Outcome.rel_eq_iff (a b : Outcome ρ r) :
    Outcome.Rel Eq Eq a b ↔ a = b := by
  cases a <;> cases b <;> simp [Outcome.Rel]

/-- The prototype's equality theorem is a specialization of the simulation. -/
theorem execLoop_eq_runFold
    (source target : ρ → Option (Outcome ρ r))
    (bind : v → ρ → Option ρ) (leave : ρ → ρ → Option ρ)
    (step : ∀ s, target s = (source s).map Outcome.lower)
    (env : ρ) (items : List v) :
    execLoop source bind leave env items = runFold target bind leave env items := by
  have h := execLoop_sim Eq Eq source target bind bind leave leave
    (fun _ _ _ h => by subst_vars; exact (Related.eq_iff _ _).mpr rfl)
    (fun _ _ _ _ h hi => by subst_vars; exact (Related.eq_iff _ _).mpr rfl)
    (fun s t h => by
      subst t
      rw [step]
      cases source s <;> simp [Related, Outcome.rel_eq_iff])
    env env rfl items
  cases he : execLoop source bind leave env items <;>
    cases ht : runFold target bind leave env items <;> simp_all [Related, Outcome.rel_eq_iff]

/-- Certificates observe live locals, rather than equality of environment lists.
The language supplies the implication from its store relation to those reads. -/
theorem observe_normal
    (R : ρ → σ → Prop) (V : r → q → Prop)
    (live : List String) (readS : ρ → String → Option α) (readT : σ → String → Option α)
    (observes : ∀ s t, R s t → ∀ n ∈ live, readS s n = readT t n)
    (s : ρ) (t : σ)
    (h : Related (Outcome.Rel R V) (some (.normal s)) (some (.normal t))) :
    ∀ n ∈ live, readS s n = readT t n :=
  observes s t h

def lowerLoop (changed : List (String × IR.Ty T)) (binder : String)
    (elem : IR.Ty T) (body : IR.Body T E) (items : IR.Expr T E)
    (rest : IR.Body T E) (breaks : Bool) (returns : Option (IR.Ty T))
    (scope : List (String × IR.Ty T) := []) : IR.Body T E :=
  .fold (changed.map Prod.fst) binder body items rest
    { span := default, stateTypes := changed.map Prod.snd, elem, scope,
      breaks := breaks || returns.isSome, returns }

end tolean.Core.Loop
