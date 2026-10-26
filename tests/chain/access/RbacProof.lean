import tolean.Audit
import access.RbacSpec

namespace Proof
open access.Rbac

/-- A loop that sets a flag when an item meets `c` computes `any`. -/
private theorem fold_flag {A : Type} (c : A → Bool) :
    ∀ (xs : List A) (b : Bool),
      xs.foldl (fun found x => if c x = true then true else found) b = (b || xs.any c) := by
  intro xs
  induction xs with
  | nil => intro b; simp
  | cons x rest ih =>
    intro b
    simp only [List.foldl_cons, List.any_cons]
    rw [ih]
    cases c x <;> simp

theorem allowed_eq (p : Policy) (req : Request) :
    allowed p req = p.bindings.any (bindingAllows p · req) := by
  have h : allowed p req =
      p.bindings.foldl (fun found x => if bindingAllows p x req = true then true else found) false :=
    rfl
  rw [h, fold_flag]
  simp

theorem denied_eq (p : Policy) (req : Request) :
    denied p req = p.denies.any (denyApplies p · req) := by
  have h : denied p req =
      p.denies.foldl (fun found x => if denyApplies p x req = true then true else found) false :=
    rfl
  rw [h, fold_flag]
  simp

theorem permits_eq (p : Policy) (req : Request) :
    permits p req = (p.bindings.any (bindingAllows p · req) && !p.denies.any (denyApplies p · req)) := by
  simp only [permits, allowed_eq, denied_eq]

theorem tenant_isolation : Spec.tenant_isolation := by
  intro p req b d hb hd
  let q : Policy := { p with bindings := p.bindings ++ [b], denies := p.denies ++ [d] }
  have hq : ∀ x, bindingAllows q x req = bindingAllows p x req := fun _ => rfl
  have hq' : ∀ x, denyApplies q x req = denyApplies p x req := fun _ => rfl
  have hb' : bindingAllows p b req = false := by simp [bindingAllows, hb]
  have hd' : denyApplies p d req = false := by simp [denyApplies, hd]
  show permits q req = permits p req
  rw [permits_eq, permits_eq]
  simp only [hq, hq', q, List.any_append, List.any_cons, List.any_nil, hb', hd', Bool.or_false]

theorem deny_wins : Spec.deny_wins := by
  intro p req d hmem happ
  rw [permits_eq]
  have : p.denies.any (denyApplies p · req) = true := List.any_eq_true.mpr ⟨d, hmem, happ⟩
  simp [this]

theorem needs_binding : Spec.needs_binding := by
  intro p req h
  rw [permits_eq] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨b, hmem, hb⟩ := List.any_eq_true.mp h.1
  simp only [bindingAllows, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨b, hmem, hb.1.1, hb.1.2, hb.2⟩

theorem group_grants : Spec.group_grants := by
  intro p req b hmem ht hg hr hd
  rw [permits_eq, ← denied_eq, hd]
  have : bindingAllows p b req = true := by simp [bindingAllows, isMember, ht, hg, hr]
  have hany : p.bindings.any (bindingAllows p · req) = true := List.any_eq_true.mpr ⟨b, hmem, this⟩
  simp [hany]

theorem deny_never_grants : Spec.deny_never_grants := by
  intro p req d h
  have hb : ∀ x, bindingAllows { p with denies := p.denies ++ [d] } x req = bindingAllows p x req :=
    fun _ => rfl
  have hd : ∀ x, denyApplies { p with denies := p.denies ++ [d] } x req = denyApplies p x req :=
    fun _ => rfl
  rw [permits_eq] at h ⊢
  simp only [hb, hd, List.any_append, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at h
  simp [h.1, h.2.1]

end Proof

#audit_claims Spec Proof
