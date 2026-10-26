import tolean.Audit
import theorems.«Sort.spec»

namespace Proof
open Sorting

/-- Insert `x` before the first element that is at least `x`. -/
def ins (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

/-- Once `x` is placed, the loop copies the rest. -/
theorem loop_placed (x : Int) : ∀ (ys out : List Int) (i : Int),
    Insert.loop1 x i ys true out = pure (.inl (true, out ++ ys))
  | [], out, i => by simp [Insert.loop1]
  | y :: ys, out, i => by
    simp [Insert.loop1, loop_placed x ys]

/-- Before `x` is placed, the loop and a final append build `out ++ ins x ys`. -/
theorem loop_unplaced (x : Int) : ∀ (ys out : List Int) (i : Int),
    (match (Insert.loop1 x i ys false out).run with
      | .inl (p, o) => if p then o else o ++ [x]
      | .inr r => r) = out ++ ins x ys
  | [], out, i => by simp [Insert.loop1, ins, Id.run] <;> rfl
  | y :: ys, out, i => by
    by_cases h : x ≤ y
    · simp [Insert.loop1, ins, h, loop_placed, Id.run] <;> rfl
    · have := loop_unplaced x ys (out ++ [y]) (i + 1)
      simp [Insert.loop1, ins, h, Id.run] at this ⊢
      simpa using this

theorem insert_eq (xs : List Int) (x : Int) : Sorting.Insert xs x = ins x xs := by
  have := loop_unplaced x xs [] 0
  unfold Sorting.Insert
  simp only [Id.run] at this ⊢
  split at this
  · next p o heq => rw [heq]; cases p <;> simp at this <;> exact this
  · next r heq => rw [heq]; exact this

theorem sort_loop (xs out : List Int) (i : Int) :
    «Sort».loop1 i xs out = pure (.inl (xs.foldl (fun acc x => ins x acc) out)) := by
  induction xs generalizing out i with
  | nil => simp [«Sort».loop1]
  | cons x xs ih => simp [«Sort».loop1, ih, insert_eq]

theorem sort_eq (xs : List Int) : «Sort» xs = xs.foldl (fun acc x => ins x acc) [] := by
  simp [«Sort», sort_loop, Id.run]; rfl

theorem ins_perm (x : Int) : ∀ ys : List Int, (ins x ys).Perm (x :: ys)
  | [] => by simp [ins]
  | y :: ys => by
    unfold ins
    split
    · exact List.Perm.refl _
    · exact ((ins_perm x ys).cons y).trans (List.Perm.swap x y ys)

theorem ins_sorted (x : Int) : ∀ ys : List Int, ys.Pairwise (· ≤ ·) →
    (ins x ys).Pairwise (· ≤ ·)
  | [], _ => by simp [ins]
  | y :: ys, h => by
    unfold ins
    split
    · next hxy =>
      refine List.Pairwise.cons ?_ h
      intro z hz
      simp at hz
      rcases hz with rfl | hz
      · exact hxy
      · exact Int.le_trans hxy ((List.pairwise_cons.mp h).1 z hz)
    · next hxy =>
      have hy := (List.pairwise_cons.mp h)
      refine List.Pairwise.cons ?_ (ins_sorted x ys hy.2)
      intro z hz
      have hz' := (ins_perm x ys).mem_iff.mp hz
      simp at hz'
      rcases hz' with rfl | hz'
      · omega
      · exact hy.1 z hz'

theorem fold_sorted : ∀ (xs out : List Int), out.Pairwise (· ≤ ·) →
    (xs.foldl (fun acc x => ins x acc) out).Pairwise (· ≤ ·)
  | [], _, h => h
  | x :: xs, out, h => fold_sorted xs (ins x out) (ins_sorted x out h)

theorem fold_perm : ∀ (xs out : List Int),
    (xs.foldl (fun acc x => ins x acc) out).Perm (out ++ xs)
  | [], out => by simp
  | x :: xs, out => by
    have := fold_perm xs (ins x out)
    refine this.trans ?_
    have h1 : (ins x out ++ xs).Perm ((x :: out) ++ xs) := (ins_perm x out).append_right xs
    refine h1.trans ?_
    simpa using (List.perm_middle (a := x) (l₁ := out) (l₂ := xs)).symm

theorem sort_sorted : Spec.sort_sorted := by
  intro xs
  rw [sort_eq]
  exact fold_sorted xs [] List.Pairwise.nil

theorem sort_perm : Spec.sort_perm := by
  intro xs
  rw [sort_eq]
  simpa using fold_perm xs []

end Proof

#audit_claims Spec Proof
