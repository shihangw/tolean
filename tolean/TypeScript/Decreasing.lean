import Lean

/-!
The proof that a translated recursive function ends.

The translator accepts a function that calls itself only when each call
passes a part of one parameter: a field of it, a value that a `match`
narrows it to, an element of a list in it, or a part of one of these
(`IR.Body.decreasingParam?`). The output then ends the function with

```lean
termination_by p
decreasing_by all_goals tolean_decreasing
```

so Lean measures `p` by `sizeOf` and runs `tolean_decreasing` on the goal of
each call. Each step of a part makes the value smaller: `sizeOf` of a
structure is one more than the sum of its fields, `sizeOf (some x)` is one
more than `sizeOf x`, and an element of a list is smaller than the list.
The tactic splits each structure into its fields, so that `simp` sees these
sums, and `omega` adds them up.

Lean adds the fact `x ∈ xs` to the goal of a call in the function of
`List.map xs f`, and of `List.filter` and `List.foldl`. The `wf_preprocess`
lemmas below do the same for `List.any`, `List.all` and `List.find?`, which
the output also writes.

Nothing here is trusted: Lean checks every proof that the tactic builds, and
refuses the output when the tactic fails.
-/

open Lean Meta Elab Tactic

namespace tolean.TypeScript.Decreasing

/-- Split each local whose type is a structure into its fields, and the
fields that are structures too, at most `depth` times. -/
partial def splitStructs (depth : Nat) : TacticM Unit := withMainContext do
  if depth == 0 then return
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR d.type
    if let some n := ty.getAppFn.constName? then
      if isStructure (← getEnv) n then
        let goals ← (← getMainGoal).cases d.fvarId
        replaceMainGoal (goals.map (·.mvarId)).toList
        splitStructs (depth - 1)
        return

/-- Split each structure among the locals into its fields. -/
elab "tolean_split_structs" : tactic => splitStructs 256

/-- For each local `h : x ∈ xs` of a list `xs`, add `sizeOf x < sizeOf xs`. -/
elab "tolean_mem_sizes" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    unless (← instantiateMVars d.type).isAppOfArity ``Membership.mem 5 do continue
    try
      let proof ← mkAppM ``List.sizeOf_lt_of_mem #[d.toExpr]
      let (_, goal) ← (← (← getMainGoal).assert `hsize (← inferType proof) proof).intro1P
      replaceMainGoal [goal]
    catch _ => pure ()

end tolean.TypeScript.Decreasing

/-- The proof that a call of a recursive function of the output passes a
smaller value, by `sizeOf`, than the function got. -/
macro "tolean_decreasing" : tactic => `(tactic| (
  simp_wf
  tolean_mem_sizes
  tolean_split_structs
  all_goals (simp_all (config := { zetaDelta := true }); try omega)))

namespace List

variable {α : Type}

@[wf_preprocess] theorem any_wfParam_tolean {xs : List α} {f : α → Bool} :
    (wfParam xs).any f = xs.attach.unattach.any f := by
  simp [wfParam]

@[wf_preprocess] theorem any_unattach_tolean {P : α → Prop} {xs : List (Subtype P)} {f : α → Bool} :
    xs.unattach.any f = xs.any fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

@[wf_preprocess] theorem all_wfParam_tolean {xs : List α} {f : α → Bool} :
    (wfParam xs).all f = xs.attach.unattach.all f := by
  simp [wfParam]

@[wf_preprocess] theorem all_unattach_tolean {P : α → Prop} {xs : List (Subtype P)} {f : α → Bool} :
    xs.unattach.all f = xs.all fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

@[wf_preprocess] theorem find?_wfParam_tolean {xs : List α} {f : α → Bool} :
    (wfParam xs).find? f = xs.attach.unattach.find? f := by
  simp [wfParam]

@[wf_preprocess] theorem find?_unattach_tolean {P : α → Prop} {xs : List (Subtype P)} {f : α → Bool} :
    xs.unattach.find? f = (xs.find? fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x)).map Subtype.val := by
  simp only [wfParam, binderNameHint]
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨y, hy⟩ := y
    simp only [unattach_cons, find?_cons]
    cases f y <;> simp [ih]

end List
