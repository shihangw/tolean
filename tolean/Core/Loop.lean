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

private theorem execLoop_cons (body : ρ → Option (Outcome ρ r))
    (bind : v → ρ → Option ρ) (leave : ρ → ρ → Option ρ)
    (env : ρ) (x : v) (xs : List v) :
    execLoop body bind leave env (x :: xs) =
      (bind x env).bind fun inner =>
        (body inner).bind fun outcome =>
          match outcome with
          | .ret value => some (.ret value)
          | .normal state | .cont state =>
            (leave env state).bind fun next => execLoop body bind leave next xs
          | .brk state => (leave env state).map Outcome.normal := by
  cases hb : bind x env with
  | none => simp [execLoop, hb]
  | some inner =>
    cases ho : body inner with
    | none => simp [execLoop, hb, ho]
    | some out =>
      cases out with
      | ret value => simp [execLoop, hb, ho]
      | normal state => simp [execLoop, hb, ho]
      | cont state => simp [execLoop, hb, ho]
      | brk state =>
        cases hl : leave env state <;> simp [execLoop, hb, ho, hl]

private theorem runFold_cons (body : σ → Option (Outcome σ q))
    (bind : v → σ → Option σ) (leave : σ → σ → Option σ)
    (env : σ) (x : v) (xs : List v) :
    runFold body bind leave env (x :: xs) =
      (bind x env).bind fun inner =>
        (body inner).bind fun outcome =>
          match outcome with
          | .ret value => some (.ret value)
          | .normal state =>
            (leave env state).bind fun next => runFold body bind leave next xs
          | .brk state => (leave env state).map Outcome.normal
          | .cont _ => none := by
  cases hb : bind x env with
  | none => simp [runFold, hb]
  | some inner =>
    cases ho : body inner with
    | none => simp [runFold, hb, ho]
    | some out =>
      cases out with
      | ret value => simp [runFold, hb, ho]
      | normal state => simp [runFold, hb, ho]
      | cont state => simp [runFold, hb, ho]
      | brk state =>
        cases hl : leave env state <;> simp [runFold, hb, ho, hl]

/-- `R` relates stores between iterations. `I s t` relates stores inside the
iteration entered from `s` and `t`: it includes the body's agreement and frame
facts. Binding establishes this anchored relation, the body preserves it, and
scope exit converts it back to `R`. Return payloads do not require a frame. -/
theorem execLoop_sim
    (R : ρ → σ → Prop) (V : r → q → Prop)
    (I : ρ → σ → ρ → σ → Prop)
    (source : ρ → Option (Outcome ρ r)) (target : σ → Option (Outcome σ q))
    (bindS : v → ρ → Option ρ) (bindT : v → σ → Option σ)
    (leaveS : ρ → ρ → Option ρ) (leaveT : σ → σ → Option σ)
    (bindLaw : ∀ x s t, R s t → Related (I s t) (bindS x s) (bindT x t))
    (leaveLaw : ∀ s t si ti, R s t → I s t si ti →
      Related R (leaveS s si) (leaveT t ti))
    (bodyLaw : ∀ s t si ti, R s t → I s t si ti →
      Related (fun a b => Outcome.Rel (I s t) V a.lower b) (source si) (target ti))
    (s : ρ) (t : σ) (initial : R s t) (items : List v) :
    Related (Outcome.Rel R V)
      (execLoop source bindS leaveS s items) (runFold target bindT leaveT t items) := by
  induction items generalizing s t with
  | nil => exact initial
  | cons x xs ih =>
    simp only [execLoop, runFold]
    apply Related.bind (bindLaw x s t initial)
    intro si ti bound
    apply Related.bind (bodyLaw s t si ti initial bound)
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
  have h := execLoop_sim Eq Eq (fun _ _ si ti => si = ti)
    source target bind bind leave leave
    (fun _ _ _ h => by subst_vars; exact (Related.eq_iff _ _).mpr rfl)
    (fun _ _ _ _ h hi => by subst_vars; exact (Related.eq_iff _ _).mpr rfl)
    (fun _ _ s t _ h => by
      subst t
      rw [step]
      cases source s <;> simp [Related, Outcome.rel_eq_iff])
    env env rfl items
  cases he : execLoop source bind leave env items <;>
    cases ht : runFold target bind leave env items <;> simp_all [Related, Outcome.rel_eq_iff]

/-- If the target loop succeeds, the source loop succeeds with a related
result. The step law covers binding and the body together. It therefore does
not require a partial source binder to succeed when the target body rejects an
element. `I` relates body exits to the stores that the loop entered with; it
does not have to relate body entries to those exits. -/
private def loopStep (body : ρ → Option (Outcome ρ r))
    (bind : v → ρ → Option ρ) (x : v) (env : ρ) : Option (Outcome ρ r) :=
  (bind x env).bind body

private theorem execLoop_step (body : ρ → Option (Outcome ρ r))
    (bind : v → ρ → Option ρ) (leave : ρ → ρ → Option ρ)
    (env : ρ) (x : v) (xs : List v) :
    execLoop body bind leave env (x :: xs) =
      match loopStep body bind x env with
      | none => none
      | some (.ret value) => some (.ret value)
      | some (.normal inner) | some (.cont inner) =>
        (leave env inner).bind fun next => execLoop body bind leave next xs
      | some (.brk inner) => (leave env inner).map Outcome.normal := by
  cases hb : bind x env with
  | none => simp [execLoop, loopStep, hb]
  | some inner =>
    cases ho : body inner with
    | none => simp [execLoop, loopStep, hb, ho]
    | some out =>
      cases out with
      | ret value => simp [execLoop, loopStep, hb, ho]
      | normal state => simp [execLoop, loopStep, hb, ho]
      | cont state => simp [execLoop, loopStep, hb, ho]
      | brk state =>
        cases hl : leave env state <;> simp [execLoop, loopStep, hb, ho, hl]

private theorem runFold_step (body : σ → Option (Outcome σ q))
    (bind : v → σ → Option σ) (leave : σ → σ → Option σ)
    (env : σ) (x : v) (xs : List v) :
    runFold body bind leave env (x :: xs) =
      match loopStep body bind x env with
      | none => none
      | some (.ret value) => some (.ret value)
      | some (.normal inner) =>
        (leave env inner).bind fun next => runFold body bind leave next xs
      | some (.brk inner) => (leave env inner).map Outcome.normal
      | some (.cont _) => none := by
  cases hb : bind x env with
  | none => simp [runFold, loopStep, hb]
  | some inner =>
    cases ho : body inner with
    | none => simp [runFold, loopStep, hb, ho]
    | some out =>
      cases out with
      | ret value => simp [runFold, loopStep, hb, ho]
      | normal state => simp [runFold, loopStep, hb, ho]
      | cont state => simp [runFold, loopStep, hb, ho]
      | brk state =>
        cases hl : leave env state <;> simp [runFold, loopStep, hb, ho, hl]

theorem execLoop_refines
    (R : ρ → σ → Prop) (V : r → q → Prop)
    (I : ρ → σ → ρ → σ → Prop)
    (source : ρ → Option (Outcome ρ r)) (target : σ → Option (Outcome σ q))
    (bindS : v → ρ → Option ρ) (bindT : v → σ → Option σ)
    (leaveS : ρ → ρ → Option ρ) (leaveT : σ → σ → Option σ)
    (leaveLaw : ∀ s t si ti, R s t → I s t si ti →
      Related R (leaveS s si) (leaveT t ti))
    (stepLaw : ∀ x s t, R s t →
      ∀ b, loopStep target bindT x t = some b →
        ∃ a, loopStep source bindS x s = some a ∧ Outcome.Rel (I s t) V a.lower b)
    (s : ρ) (t : σ) (initial : R s t) (items : List v) :
    ∀ {b}, runFold target bindT leaveT t items = some b →
      ∃ a, execLoop source bindS leaveS s items = some a ∧ Outcome.Rel R V a b := by
  induction items generalizing s t with
  | nil =>
    intro b h
    simp only [runFold] at h
    cases b <;> simp_all
    exact ⟨.normal s, by simp [execLoop], initial⟩
  | cons x xs ih =>
    intro b h
    rw [runFold_step] at h
    cases htarget : loopStep target bindT x t with
    | none => simp [htarget] at h
    | some outT =>
      simp only [htarget] at h
      obtain ⟨outS, hsource, hrel⟩ := stepLaw x s t initial outT htarget
      cases outT with
      | ret value =>
        have hbResult : b = .ret value := by simpa using h.symm
        subst b
        cases outS with
        | ret sourceValue =>
          have hvalue : V sourceValue value := by
            simpa [Outcome.lower, Outcome.Rel] using hrel
          refine ⟨.ret sourceValue, ?_, ?_⟩
          · simp [execLoop_step, hsource]
          · simpa [Outcome.Rel] using hvalue
        | normal _ => simp [Outcome.lower, Outcome.Rel] at hrel
        | brk _ => simp [Outcome.lower, Outcome.Rel] at hrel
        | cont _ => simp [Outcome.lower, Outcome.Rel] at hrel
      | normal innerT =>
        cases outS with
        | normal innerS =>
          have hinner : I s t innerS innerT := by
            simpa [Outcome.lower, Outcome.Rel] using hrel
          cases hlt : leaveT t innerT with
          | none => simp [hlt] at h
          | some nextT =>
            have hnext : runFold target bindT leaveT nextT xs = some b := by
              simpa [hlt] using h
            have hleave := leaveLaw s t innerS innerT initial hinner
            rw [hlt] at hleave
            cases hls : leaveS s innerS with
            | none => simp [Related, hls] at hleave
            | some nextS =>
              have hnextRel : R nextS nextT := by
                simpa [Related, hls] using hleave
              obtain ⟨out, hexec, hout⟩ := ih nextS nextT hnextRel hnext
              refine ⟨out, ?_, hout⟩
              simpa [execLoop_step, hsource, hls] using hexec
        | cont innerS =>
          have hinner : I s t innerS innerT := by
            simpa [Outcome.lower, Outcome.Rel] using hrel
          cases hlt : leaveT t innerT with
          | none => simp [hlt] at h
          | some nextT =>
            have hnext : runFold target bindT leaveT nextT xs = some b := by
              simpa [hlt] using h
            have hleave := leaveLaw s t innerS innerT initial hinner
            rw [hlt] at hleave
            cases hls : leaveS s innerS with
            | none => simp [Related, hls] at hleave
            | some nextS =>
              have hnextRel : R nextS nextT := by
                simpa [Related, hls] using hleave
              obtain ⟨out, hexec, hout⟩ := ih nextS nextT hnextRel hnext
              refine ⟨out, ?_, hout⟩
              simpa [execLoop_step, hsource, hls] using hexec
        | ret _ => simp [Outcome.lower, Outcome.Rel] at hrel
        | brk _ => simp [Outcome.lower, Outcome.Rel] at hrel
      | brk innerT =>
        cases outS with
        | brk innerS =>
          have hinner : I s t innerS innerT := by
            simpa [Outcome.lower, Outcome.Rel] using hrel
          cases hlt : leaveT t innerT with
          | none => simp [hlt] at h
          | some nextT =>
            have hbResult : b = .normal nextT := by
              simpa [hlt] using h.symm
            subst b
            have hleave := leaveLaw s t innerS innerT initial hinner
            rw [hlt] at hleave
            cases hls : leaveS s innerS with
            | none => simp [Related, hls] at hleave
            | some nextS =>
              have hnextRel : R nextS nextT := by
                simpa [Related, hls] using hleave
              refine ⟨.normal nextS, ?_, hnextRel⟩
              simp [execLoop_step, hsource, hls]
        | ret _ => simp [Outcome.lower, Outcome.Rel] at hrel
        | normal _ => simp [Outcome.lower, Outcome.Rel] at hrel
        | cont _ => simp [Outcome.lower, Outcome.Rel] at hrel
      | cont _ => simp at h

/-- Exact simulation is a special case of the one-way refinement. -/
theorem execLoop_sim_refines
    (R : ρ → σ → Prop) (V : r → q → Prop)
    (I : ρ → σ → ρ → σ → Prop)
    (source : ρ → Option (Outcome ρ r)) (target : σ → Option (Outcome σ q))
    (bindS : v → ρ → Option ρ) (bindT : v → σ → Option σ)
    (leaveS : ρ → ρ → Option ρ) (leaveT : σ → σ → Option σ)
    (bindLaw : ∀ x s t, R s t → Related (I s t) (bindS x s) (bindT x t))
    (leaveLaw : ∀ s t si ti, R s t → I s t si ti →
      Related R (leaveS s si) (leaveT t ti))
    (bodyLaw : ∀ s t si ti, R s t → I s t si ti →
      Related (fun a b => Outcome.Rel (I s t) V a.lower b) (source si) (target ti))
    (s : ρ) (t : σ) (initial : R s t) (items : List v)
    {b} (h : runFold target bindT leaveT t items = some b) :
    ∃ a, execLoop source bindS leaveS s items = some a ∧ Outcome.Rel R V a b := by
  apply execLoop_refines R V I source target bindS bindT leaveS leaveT
    leaveLaw
    (fun x s t hs b hstep => ?_) s t initial items h
  cases hbt : bindT x t with
  | none => simp [loopStep, hbt] at hstep
  | some ti =>
    have hbind := bindLaw x s t hs
    rw [hbt] at hbind
    cases hbs : bindS x s with
    | none => simp [Related, hbs] at hbind
    | some si =>
      have hentry : I s t si ti := by
        simpa [Related, hbs] using hbind
      cases hbody : target ti with
      | none => simp [loopStep, hbt, hbody] at hstep
      | some outT =>
        have hb : b = outT := by
          simpa [loopStep, hbt, hbody] using hstep.symm
        subst b
        have hbodyRel := bodyLaw s t si ti hs hentry
        rw [hbody] at hbodyRel
        cases hsource : source si with
        | none => simp [Related, hsource] at hbodyRel
        | some outS =>
          have hrel : Outcome.Rel (I s t) V outS.lower outT := by
            simpa [Related, hsource] using hbodyRel
          refine ⟨outS, ?_, hrel⟩
          simp [loopStep, hbs, hsource]

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

def lowerLoop (span : Span) (changed : List (String × IR.Ty T)) (binder : String)
    (elem : IR.Ty T) (body : IR.Body T E) (items : IR.Expr T E)
    (rest : IR.Body T E) (breaks : Bool) (returns : Option (IR.Ty T))
    (scope : List (String × IR.Ty T) := []) : IR.Body T E :=
  .fold (changed.map Prod.fst) binder body items rest
    { span, stateTypes := changed.map Prod.snd, elem, scope,
      breaks := breaks || returns.isSome, returns }

end tolean.Core.Loop
