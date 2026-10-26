import src.Sorting

namespace Spec
open Sorting

/-- The output of `sort` is in ascending order. -/
def sort_sorted : Prop :=
  ∀ xs : List Int, (sort xs).Pairwise (· ≤ ·)

/-- The output of `sort` has the same elements as the input, with the same
counts. Without this claim, a sort that returns `[]` would pass. -/
def sort_perm : Prop :=
  ∀ xs : List Int, (sort xs).Perm xs

end Spec
