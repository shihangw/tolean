# Plan: say which functions check their own inputs

**Status:** planned, not built · **Date:** 2026-11-03

A theorem about a function often has a precondition: it holds only for
inputs that meet a condition. The claim in the sample project is an example:

```lean
∀ (g : Gauge) (step : Int), g.level ≤ g.max → (raise g step).level ≤ (raise g step).max
```

Tolean does not change the code that runs, so it cannot add a check of
`g.level ≤ g.max` to it. Either the code that calls `raise` makes sure that
the condition holds, or the function checks it itself, in its source:

```ts
export function raiseChecked(g: Gauge, step: bigint): Gauge | null {
  if (g.level > g.max) return null;
  return raise(g, step);
}
```

Then the claim about `raiseChecked` has no precondition: for every `g` and
`step`, the result is `null` or a gauge whose level is at most its maximum.
Nothing about the inputs is left to trust, because the check is code that
runs and the proof covers it.

By default, a function's inputs stay trusted, and the callers are responsible
for them. This plan lets a project say in `tolean.json` which functions check
their own inputs instead, and has `tolean chain check` hold them to it. It also
has `tolean chain trust` list the preconditions that the callers must meet,
so that a project no longer writes that node by hand.

## The setting

`checkInputs` is a setting of an entry in `overrides`, as `certify` is. It
names the functions of the matched files whose inputs the function checks:

```json
"typescript": {
  "sources": ["src/**/*.ts"],
  "overrides": [
    { "sources": ["src/api/*.ts"], "checkInputs": true },
    { "sources": ["src/sensor/raise.ts"], "checkInputs": ["raiseChecked"] }
  ]
}
```

`true` names every exported function of the matched files, because exported
functions are where other code enters. A list names the functions by their
names in the source. A name that the matched files do not declare makes
`tolean translate` fail. Without the setting, a function's inputs are trusted.

## How the setting reaches the check

`tolean translate` writes the setting into each file's chain manifest, such as
`sensor/Raise.lean.chain.json`, as a list `checkInputs` of the functions'
names in Lean, such as `sensor.Raise.raiseChecked`. The translator knows which
Lean name each source function gets, and the manifest already records what
the file relies on. So `tolean chain check` needs to read only the manifests,
as it does now.

## What `chain check` does

A precondition is a hypothesis at the top of a claim: a binder of the claim's
`∀` whose type is a proposition, such as `g.level ≤ g.max`. `chain check`
already imports the claims from the built `.olean` files. It unfolds each
claim's definition and walks its binders in Lean's `MetaM`, so it can ask
exactly which binder types are propositions. Instance arguments, such as
`[JSNumber N]`, are not preconditions on the inputs: they are assumptions
about the model of numbers, which the table of links lists as its own link.

The check then fails in two cases:

- **A claim about a function that checks its inputs has a precondition.** A
  claim is about a function when its statement names the function. The
  message names the claim, the function and the precondition, such as:
  `claim raise_ok is about sensor.Raise.raiseChecked, whose inputs
  tolean.json says the function checks, but it assumes g.level ≤ g.max`.
- **A function that checks its inputs has no claim.** Without a claim, nothing
  proves that the function checks anything, so the setting would promise
  more than the chain holds.

## What `chain trust` lists

For every claim with a precondition, `chain trust <claim>` lists the inputs
as trusted, with each precondition as Lean prints it:

```
trusted: the inputs of raise_stays_under_max: callers must make g.level ≤ g.max hold
```

So a project no longer needs a node such as `callers` in
`tests/chain/tolean.chain.json` for this. A node that a project writes
itself still works, for anything else that it trusts.

## What it does not see

The check finds a precondition only where the claim states it as a
hypothesis, after its `∀`. That is the usual form, and the form that
`raise_stays_under_max` has. A condition hidden inside the conclusion, such
as `¬ (g.level ≤ g.max) ∨ …`, is not a hypothesis, so the check does not see
it. A person who reads the claim still does. The docs of the setting say
this.

The check also trusts that a function's callers call the function that the
setting names. If a module exports both `raise` and `raiseChecked`, other
code can still call `raise`. To rule that out, the module exports only the
function that checks, and `tsc` then refuses a call of the other one from
another file.

## Steps

1. Read `checkInputs` in `tolean/Project.lean`, for each language that has
   functions, and refuse a name that the matched files do not declare.
2. Write the setting into each file's chain manifest, in
   `tolean/Chain/Emit.lean` and `tolean/Chain/Manifest.lean`.
3. Find the preconditions of a claim in `tolean/Chain/Check.lean`, and add the
   two failures to `chain check`.
4. List the trusted inputs in `chain trust`, and drop the `callers` node from
   the sample project.
5. Add cases to `tests/chain/check.sh`: a claim with a precondition about a
   function that checks its inputs fails, a function that checks its inputs
   and has no claim fails, and `chain trust` prints the precondition of
   `raise_stays_under_max`.
6. Describe the setting in the README's section on the project file, and in
   the Inputs row of the table of links.

## Open questions

- Should `checkInputs` also apply to Go, where an interface call is a step
  whose result the proof does not control? The setting would say that the
  function checks what the step returns, as well as its arguments.
- Should a claim be able to say which function it is about, for a claim that
  names several functions?
