# String-keyed records need a lookup condition

We intend to accept `Record<string, V>`, both as a named type and in place.
`Readonly` does not change its runtime meaning. A lookup has type
`V | undefined`, as it does under `noUncheckedIndexedAccess`.

A dynamic lookup must carry a condition in its certificate and in
`program_sound`: the key is an own key of the record, or it is not a name
on `Object.prototype`. JavaScript can otherwise return an inherited
function rather than a value of type `V`. The condition must describe the
record and key at the lookup, not merely the function's initial arguments.

An `Object.hasOwn(record, key)` guard discharges that condition.
Iteration through `Object.keys` or `Object.entries` also establishes that
the key is an own key. These forms should need no extra hypothesis.
The guide should teach the guarded form when it is supported.
Literal inherited names, such as `toString` and `constructor`, stay refused
for these dictionaries. Record literals with `__proto__` stay refused
because that spelling can set the prototype rather than an own property.

## Current boundary

This change improves the refusal instead of enabling dictionary operations.
The existing translation represents a record as a structure with a fixed
list of fields. Its `recordIndex` requires a declared literal union, and
`recordGet` selects one of those fields. That representation cannot store
an arbitrary runtime key set.

The source evaluator already distinguishes absent own properties from
inherited properties in `Spec.getKey`. Reusing a map lookup that returns
`undefined` for every missing key would disagree with that evaluator.
Accepting string keys requires a dictionary representation and a proof
that transports the lookup condition through branches and calls.
Neither is supplied here, so named and inline string-keyed records remain
refused, including their `Readonly` forms. Naming the type does not solve
this problem, and the diagnostic now says so.

No runtime feature or edition is added in this slice. A later implementation
must record `OrdinaryGet` (ECMA-262 2024 §10.1.8.1) and
`Object.hasOwn` (§20.1.2.13, introduced in ES2022) in `Edition.lean`,
cover the operations through `program_sound`, and compare them with
JavaScript in `interpreter.test.ts`. It must also test keys from
`Object.keys` and `Object.entries`, missing keys, inherited names, and
the order of own keys.
