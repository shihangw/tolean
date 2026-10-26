import tolean.Audit
import theorems.«Sort.spec»

namespace Proof
open Sorting

/-- Insert `x` before the first element that is at least `x`. -/
def ins (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

/-- One turn of the loop in `insert`, on the pair `(out, placed)`. -/
def step (x : Int) (acc : List Int × Bool) (y : Int) : List Int × Bool :=
  if !acc.2 && decide (x ≤ y) then (acc.1 ++ [x] ++ [y], true) else (acc.1 ++ [y], acc.2)

/-- After the loop, `insert` appends `x` if no element was larger. -/
def finish (x : Int) (acc : List Int × Bool) : List Int :=
  if !acc.2 then acc.1 ++ [x] else acc.1

/-- A loop body that acts like `step` on every pair gives the same fold. -/
theorem foldl_like_step (x : Int) {f : List Int × Bool → Int → List Int × Bool}
    (hf : ∀ out placed y, f (out, placed) y = step x (out, placed) y) :
    ∀ (ys : List Int) (acc : List Int × Bool), ys.foldl f acc = ys.foldl (step x) acc
  | [], _ => rfl
  | y :: ys, (out, placed) => by
    simp only [List.foldl, hf]
    exact foldl_like_step x hf ys _

/-- `insert` is the fold of `step`, then `finish`. -/
theorem insert_eq_fold (xs : List Int) (x : Int) :
    Sorting.insert xs x = finish x (xs.foldl (step x) ([], false)) := by
  unfold Sorting.insert finish
  dsimp only
  rw [foldl_like_step x (fun out placed y => by
    cases placed <;> by_cases h : x ≤ y <;> simp [step, h])]
  -- Lean 4.30 closes the goal with the rewrite; a newer Lean may leave it.
  all_goals
    generalize List.foldl (step x) ([], false) xs = r
    obtain ⟨out, placed⟩ := r
    cases placed <;> rfl

/-- Once `x` is placed, the loop copies the rest. -/
theorem fold_placed (x : Int) : ∀ (ys out : List Int),
    ys.foldl (step x) (out, true) = (out ++ ys, true)
  | [], out => by simp
  | y :: ys, out => by simp [step, fold_placed x ys]

/-- Before `x` is placed, the loop and `finish` build `out ++ ins x ys`. -/
theorem fold_unplaced (x : Int) : ∀ (ys out : List Int),
    finish x (ys.foldl (step x) (out, false)) = out ++ ins x ys
  | [], out => by simp [finish, ins]
  | y :: ys, out => by
    by_cases h : x ≤ y
    · simp [step, h, fold_placed, finish, ins]
    · have := fold_unplaced x ys (out ++ [y])
      simp [step, h, ins] at this ⊢
      exact this

theorem insert_eq (xs : List Int) (x : Int) : Sorting.insert xs x = ins x xs := by
  rw [insert_eq_fold]
  simpa using fold_unplaced x xs []

theorem sort_eq (xs : List Int) : sort xs = xs.foldl (fun acc x => ins x acc) [] := by
  simp [sort, empty, insert_eq]

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
      have hy := List.pairwise_cons.mp h
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
    refine (fold_perm xs (ins x out)).trans ?_
    refine ((ins_perm x out).append_right xs).trans ?_
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
