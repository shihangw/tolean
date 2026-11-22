# Loop certificates compose through one result carrier

**Status:** proposed; implementation tracked in #289, WIP on branch wip/289-loop-result-carrier · **Date:** 2026-11-21

Loop certificates must compose by the meaning of their results, not by the
names Lean gives generated helpers. The certifier will keep a proof lemma for
each loop, but every early-return loop will expose its outcome through one
shared carrier. Function and parent-loop proofs can then rewrite a loop result
without depending on which match helper Lean generated for that loop.

## Failed approaches and remaining shape-1 goals

A theorem for a whole chain of loops combines different bodies and does not
scale to loops nested under branches or callbacks. Per-loop result theorems
cannot connect returning loops in the function-level link proof. Generalizing
the pair-return lemma and asking `link_eqs` to use full transparency also failed
to establish a stable rewrite boundary.

The first optional-bigint shape still leaves two link goals. The first loop
completes normally in both; the second either returns a value or also completes
normally. The proof must connect those evaluator results through translation.
Removing the carrier definitions leaves the outer evaluator and nested
`Body.runFold` unreduced, while keeping only `run` and `ofParts` leaves that fold
under the completed first-loop case.

Each loop invariant describes the current evaluator environment. In
particular, a child-loop invariant must be established after the preceding
statement has updated the accumulator. An invariant that describes the
environment at the start of the parent loop is not enough for that child.

We considered proving one theorem for a whole chain of loops. That combines
different loop bodies and their state transitions in one proof interface, so
it does not scale to loops nested under branches or callbacks. We also
considered one specialized result theorem per loop. Those lemmas remain
useful for proving each evaluator fold, but distinct per-loop result
expressions cannot by themselves connect two returning loops in the
function-level link proof.

The prototype also generalized a pair-return lemma and asked `link_eqs` to
rewrite with full transparency. That approach did not establish a stable
rewrite boundary: it still depended on unfolding the generated expression
enough to identify the result. Instead, the generator will state the shared
outcome explicitly and use the per-loop evaluator lemma only at the loop
boundary.

The implementation must retain the existing certificate claims and rejection
rules. It must not add per-shape tactic sequences, axioms, partial definitions
or weaker tests. The required regressions cover sequential returning loops
over optional and nullable bigints, nested accumulator updates, the existing
28-cell loop matrix, and two additional unreported shapes. Loop returns from
inside nested loops remain follow-up work for #289 unless the shared result
interface supports them without a shape-specific proof.

## Implementation checkpoint

The first optional-bigint shape remains blocked. The generated translation
compiles in the `Corpus.TwoReturning` namespace, but Lean rejects its
certificate in `twoReturning_link`. With all four carrier definitions in the
certificate simp set, Lean reports these exact residual goals:

```lean
case h_1
N : Type
inst✝ : JSNumber N
xs ys : List (Option Int)
result✝¹ : tolean.IR.LoopResult Bool Unit
state✝ : Unit
result✝ : tolean.IR.LoopResult Bool Unit
returned✝¹ : Option Bool
heq✝¹ :
  (forIn xs none fun x x_1 =>
        match x with
        | none => ForInStep.done (some true)
        | some x => ForInStep.yield none).run =
    none
returned✝ : Option Bool
value✝ : Bool
heq✝ :
  (forIn ys none fun x x_1 =>
        match x with
        | none => ForInStep.done (some true)
        | some x => ForInStep.yield none).run =
    some value✝
⊢ ((match
          match
            match
              (forIn ys none fun y x =>
                  match y with
                  | none => ForInStep.done (some true)
                  | some y => ForInStep.yield none).run with
            | some value => tolean.IR.LoopResult.returned value
            | none => tolean.IR.LoopResult.completed () with
          | tolean.IR.LoopResult.returned value => Outcome.ret (Except.ok (Val.bool value))
          | tolean.IR.LoopResult.completed state =>
            Outcome.normal
              [("ys", Val.list (List.map (encUndef Val.int) ys)),
                ("xs", Val.list (List.map (encUndef Val.int) xs))] with
        | Outcome.normal ρ' => some (Outcome.ret (Except.ok (Val.bool false)))
        | Outcome.ret v => some (Outcome.ret v)
        | Outcome.brk env => none
        | Outcome.cont env => none).bind
      fun __do_lift =>
      match __do_lift with
      | Outcome.ret r => some r
      | Outcome.normal env => none
      | Outcome.brk env => none
      | Outcome.cont env => none) =
    some (Except.ok (Val.bool value✝))

case h_2
N : Type
inst✝ : JSNumber N
xs ys : List (Option Int)
result✝¹ : tolean.IR.LoopResult Bool Unit
state✝¹ : Unit
result✝ : tolean.IR.LoopResult Bool Unit
state✝ : Unit
returned✝¹ : Option Bool
heq✝¹ :
  (forIn xs none fun x x_1 =>
        match x with
        | none => ForInStep.done (some true)
        | some x => ForInStep.yield none).run =
    none
returned✝ : Option Bool
heq✝ :
  (forIn ys none fun x x_1 =>
        match x with
        | none => ForInStep.done (some true)
        | some x => ForInStep.yield none).run =
    none
⊢ ((match
          match
            match
              (forIn ys none fun y x =>
                  match y with
                  | none => ForInStep.done (some true)
                  | some y => ForInStep.yield none).run with
            | some value => tolean.IR.LoopResult.returned value
            | none => tolean.IR.LoopResult.completed () with
          | tolean.IR.LoopResult.returned value => Outcome.ret (Except.ok (Val.bool value))
          | tolean.IR.LoopResult.completed state =>
            Outcome.normal
              [("ys", Val.list (List.map (encUndef Val.int) ys)),
                ("xs", Val.list (encUndef Val.int) xs)] with
        | Outcome.normal ρ' => some (Outcome.ret (Except.ok (Val.bool false)))
        | Outcome.ret v => some (Outcome.ret v)
        | Outcome.brk env => none
        | Outcome.cont env => none).bind
      fun __do_lift =>
      match __do_lift with
      | Outcome.ret r => some r
      | Outcome.normal env => none
      | Outcome.brk env => none
      | Outcome.cont env => none) =
    some (Except.ok (Val.bool false))
```

Removing all carrier definitions leaves the outer evaluator and its nested
`Body.runFold` unreduced. Keeping only `run` and `ofParts` leaves that same
nested fold under the completed first-loop case. These three simp-set choices
do not prove the first shape, so the carrier rewrite boundary still needs work.
