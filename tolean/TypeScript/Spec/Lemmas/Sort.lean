import tolean.TypeScript.Spec.Eval

/-!
What the sort of the interpreter gives (`Eval.sortValues`): the elements in
an order that ECMA-262 accepts. SortIndexedProperties (§23.1.3.30.1) asks
for a permutation of the elements in which an element comes before every
element that the comparator says is greater, and, since ES2019, in which
equal elements keep their order. With a consistent comparator only one order
does both, so `List.mergeSort` gives the order that every engine gives.

`List.mergeSort` has these facts for a relation that is total and transitive
on every value. A consistent comparator is total and transitive only on the
elements, so each fact here goes through the elements as a subtype.
-/
namespace tolean.TypeScript.Eval

open List

variable {α : Type}

/-- `List.mergeSort` sorts a list by a relation that is total and transitive
on its elements. -/
theorem pairwise_mergeSort_of_mem {le : α → α → Bool} {l : List α}
    (trans : ∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, le a b → le b c → le a c)
    (total : ∀ a ∈ l, ∀ b ∈ l, le a b || le b a) : (l.mergeSort le).Pairwise (le · ·) := by
  have h := pairwise_mergeSort (le := fun x y : {x // x ∈ l} => le x.1 y.1)
    (fun a b c => trans a.1 a.2 b.1 b.2 c.1 c.2) (fun a b => total a.1 a.2 b.1 b.2) l.attach
  have hm : (l.attach.mergeSort fun x y => le x.1 y.1).map Subtype.val =
      (l.attach.map Subtype.val).mergeSort le := map_mergeSort (fun _ _ _ _ => rfl)
  rw [attach_map_subtype_val] at hm
  rw [← hm, pairwise_map]
  exact h

/-- `List.mergeSort` keeps two elements in their order when the relation
lets the first come before the second, if the relation is total and
transitive on the elements. -/
theorem pair_sublist_mergeSort_of_mem {le : α → α → Bool} {l : List α} {a b : α}
    (trans : ∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, le a b → le b c → le a c)
    (total : ∀ a ∈ l, ∀ b ∈ l, le a b || le b a) (hab : le a b) (h : [a, b] <+ l) :
    [a, b] <+ l.mergeSort le := by
  rw [← attach_map_subtype_val l, sublist_map_iff] at h
  obtain ⟨l', hl', heq⟩ := h
  match l', heq with
  | [x, y], heq =>
    simp only [map_cons, map_nil, cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hs := pair_sublist_mergeSort (le := fun x y : {x // x ∈ l} => le x.1 y.1)
      (fun a b c => trans a.1 a.2 b.1 b.2 c.1 c.2) (fun a b => total a.1 a.2 b.1 b.2) hab hl'
    have hm : (l.attach.mergeSort fun x y => le x.1 y.1).map Subtype.val =
        (l.attach.map Subtype.val).mergeSort le := map_mergeSort (fun _ _ _ _ => rfl)
    rw [attach_map_subtype_val] at hm
    rw [← hm]
    exact hs.map Subtype.val

/-- A consistent comparator orders the elements as a total preorder: "does
not come after" is transitive and total on them. -/
theorem consistentOn_preorder {cmp : α → α → Option Ordering} {items : List α}
    (h : consistentOn cmp items = true) :
    (∀ a ∈ items, ∀ b ∈ items, ∀ c ∈ items,
      (cmp a b != some .gt) = true → (cmp b c != some .gt) = true → (cmp a c != some .gt) = true) ∧
    (∀ a ∈ items, ∀ b ∈ items, ((cmp a b != some .gt) || (cmp b a != some .gt)) = true) := by
  unfold consistentOn at h
  rw [all_eq_true] at h
  have h' : ∀ a ∈ items, ∀ b ∈ items, ((cmp a b).isSome = true ∧ cmp b a = (cmp a b).map Ordering.swap) ∧
      ∀ c ∈ items, (cmp a b != some .gt) = true → (cmp b c != some .gt) = true →
        (cmp a c != some .gt) = true := by
    intro a ha b hb
    have := h a ha
    rw [all_eq_true] at this
    have := this b hb
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, all_eq_true] at this
    refine ⟨this.1, fun c hc hab hbc => ?_⟩
    have hc' := this.2 c hc
    rw [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hc'
    rcases hc' with (h1 | h1) | h1
    · rw [hab] at h1; cases h1
    · rw [hbc] at h1; cases h1
    · exact h1
  refine ⟨fun a ha b hb c hc => (h' a ha b hb).2 c hc, fun a ha b hb => ?_⟩
  obtain ⟨⟨hsome, hswap⟩, -⟩ := h' a ha b hb
  rw [hswap]
  cases hc : cmp a b with
  | none => rw [hc] at hsome; cases hsome
  | some o => cases o <;> decide

/-- The sort gives a permutation of the elements. -/
theorem sortValues_perm {cmp : α → α → Option Ordering} {items ys : List α}
    (h : sortValues cmp items = some ys) : ys ~ items := by
  unfold sortValues at h
  split at h
  · cases h; exact mergeSort_perm _ _
  · cases h

/-- In the order that the sort gives, no element comes after one that the
comparator says is greater. -/
theorem sortValues_sorted {cmp : α → α → Option Ordering} {items ys : List α}
    (h : sortValues cmp items = some ys) : ys.Pairwise fun a b => (cmp a b != some .gt) = true := by
  unfold sortValues at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨trans, total⟩ := consistentOn_preorder hc
    exact pairwise_mergeSort_of_mem trans total
  · cases h

/-- The sort is stable: two elements that the comparator lets stay in their
order keep it. -/
theorem sortValues_stable {cmp : α → α → Option Ordering} {items ys : List α} {a b : α}
    (h : sortValues cmp items = some ys) (hab : (cmp a b != some .gt) = true) (hs : [a, b] <+ items) :
    [a, b] <+ ys := by
  unfold sortValues at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨trans, total⟩ := consistentOn_preorder hc
    exact pair_sublist_mergeSort_of_mem trans total hab hs
  · cases h

end tolean.TypeScript.Eval
