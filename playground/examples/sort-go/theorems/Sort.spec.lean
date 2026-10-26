import src.Sorting

namespace Spec
open Sorting

/-- The output of `Sort` is in ascending order. -/
def sort_sorted : Prop :=
  ∀ xs : List Int, («Sort» xs).Pairwise (· ≤ ·)

/-- The output of `Sort` has the same elements as the input, with the same
counts. Without this claim, a sort that returns `[]` would pass. -/
def sort_perm : Prop :=
  ∀ xs : List Int, («Sort» xs).Perm xs

end Spec
