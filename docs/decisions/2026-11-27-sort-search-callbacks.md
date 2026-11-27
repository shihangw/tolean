# Sort conditions inside search callbacks

**Status:** accepted · **Date:** 2026-11-27

A call to a function that sorts by number keys gives its caller a condition
over the arguments, such as "every key is finite". Before this change, a
certificate could carry that condition into a callback only for `map` and
`filter`. Step 10 of the [plan](../plans/pure-typescript.md) asked which other
callbacks can carry it, and what the rest need.

## The decision

A callback of `some`, `every`, `find` or `findIndex` now carries the condition
in the same way as `map` and `filter`. The caller's theorem takes a hypothesis
that the condition holds for every element of the callback's input list. The
callback lemma then assumes the condition only for the element that it reads.

Each of these methods visits elements of its input list in order and stops
early. So a lemma that says the callback agrees with the Lean function on
each element of the list is enough. `Proof/Link.lean` proves this for the
IR evaluator as `evalFind_find_on`, `evalFind_true_on`, `evalFind_false_on`
and `evalFindIdx_findIdx_on`. These lemmas restrict the existing lemmas, which
needed agreement for every value of the element type, to the elements of the
list. The hypothesis cannot fail for an element that the search never reaches,
because it is stated over the whole input.

The fixture `arraySortNumberSearchCallbacks.ts` must certify.

## What stays refused

These cases still fail with the error "sort conditions in this callback need
an element-restricted link lemma".

- `findLast`. The translation runs `find` on the reversed list, and the link
  proof does not yet rewrite the encoding of the reversed list into the form
  that the restricted lemma needs. The fixture
  `certify/reject/numberSortFindLastCall.ts` records the refusal.
- `reduce`. Its callback also reads the accumulator, so a condition on
  elements says nothing about the values that it reads. The fixture
  `certify/reject/numberSortReduceCall.ts` records the refusal.
- A `map` whose callback reads the index. Its lemma quantifies over the index
  as well, and it needs a restricted form over the pairs of index and element.

The other parts of step 10 are unchanged: sorts of changing loop state or of
body-local lists, the remaining computed list shapes, and direct sorts under an
enclosing nullable narrowing.
