/-!
Lemmas about `EStateM` that the proofs share. The translator's monad `TM`,
the parser's `ParseM` and the lexer's `LexM` are all `EStateM`, so a proof
about one of them uses these lemmas, under the names that its namespace
exports.
-/
namespace EStateM

variable {ε σ α β : Type}

theorem bind_ok {x : EStateM ε σ α} {f : α → EStateM ε σ β} {s s' : σ} {b : β} :
    (x >>= f) s = .ok b s' ↔ ∃ a s₁, x s = .ok a s₁ ∧ f a s₁ = .ok b s' := by
  simp only [bind, EStateM.bind]
  cases h : x s with
  | ok a s₁ =>
    simp only [EStateM.Result.ok.injEq]
    constructor
    · intro h'; exact ⟨a, s₁, ⟨rfl, rfl⟩, h'⟩
    · rintro ⟨a', s₂, ⟨rfl, rfl⟩, h'⟩; exact h'
  | error e s₁ => simp

theorem bind_eq {x : EStateM ε σ α} {f : α → EStateM ε σ β} {s s' : σ} {a : α} (h : x s = .ok a s') :
    (x >>= f) s = f a s' := by
  simp [bind, EStateM.bind, h]

theorem map_ok {x : EStateM ε σ α} {f : α → β} {s s' : σ} {b : β} :
    (f <$> x) s = .ok b s' ↔ ∃ a, x s = .ok a s' ∧ f a = b := by
  show (x >>= fun a => pure (f a)) s = .ok b s' ↔ _
  rw [bind_ok]
  simp only [pure, EStateM.pure, EStateM.Result.ok.injEq]
  constructor
  · rintro ⟨a, s₁, h, rfl, rfl⟩; exact ⟨a, h, rfl⟩
  · rintro ⟨a, h, rfl⟩; exact ⟨a, s', h, rfl, rfl⟩

@[simp] theorem ite_state {c : Prop} [Decidable c] {x y : EStateM ε σ α} {s : σ} :
    (if c then x else y) s = if c then x s else y s := by
  split <;> rfl

@[simp] theorem pure_ok {a b : α} {s s' : σ} : (pure a : EStateM ε σ α) s = .ok b s' ↔ a = b ∧ s = s' := by
  simp [pure, EStateM.pure]

@[simp] theorem get_ok {s s' c : σ} : (get : EStateM ε σ σ) s = .ok c s' ↔ c = s ∧ s' = s := by
  simp [get, getThe, MonadStateOf.get, EStateM.get]
  constructor <;> rintro ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

theorem modify_eq (f : σ → σ) (s : σ) : (modify f : EStateM ε σ PUnit) s = .ok () (f s) := rfl

end EStateM
