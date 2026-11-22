# String-keyed records use ordered association lists

`Record<string, V>` uses an ordered association list rather than a structure
with a fixed set of fields. Named types, inline types and `Readonly` forms
share this representation. Static object literals supply the properties.
A lookup has type `V | undefined`, as it does under
`noUncheckedIndexedAccess`.

Lookup compares UTF-16 code units without decoding the key. This matters
because a lone surrogate must not turn into a replacement character and
accidentally find a different property.

## Lookup certificates

The certificate generator accepts a dynamic lookup only when a direct
`Object.hasOwn(record, key)` test guards a read of that same record and key.
The generated link theorem also has a premise that the IR run succeeds.
That premise rules out dynamic reads that resolve to an inherited
`Object.prototype` property, which the record model cannot represent.
Certification also supports a local guard inside an array callback or loop
body. The per-element callback proof and loop-step proof derive ownership
from the true branch of that guard. Their helper theorems need no external
success premise. The analysis discards ownership evidence at helper entry
and after bindings, so an outer guard does not justify a later helper read.

The required certificate cases `recordGuardedCallback.ts` and
`recordGuardedLoop.ts` cover a guarded map and a guarded sum loop over
number-valued records.
The corpus reject cases `recordCallbackLookup.ts` and `recordLoopLookup.ts`
still require refusal for unguarded reads, including reads with
a constant `??` fallback: JavaScript may read an inherited
`Object.prototype` property there, so fallback evaluation does not justify
replacing that property with `undefined`. `Object.keys` and `Object.entries`
remain supported because they enumerate own properties.

Optional-valued Records use `Option.join` when printed. This makes a missing
property and an own property whose value is `undefined` both produce the
single optional result required by TypeScript.

Literal inherited names, such as `toString` and `constructor`, remain
refused for dictionary lookups. Object literals with `__proto__` also
remain refused because that spelling can set the prototype instead of
creating an own property.

## Own-key order

`Object.keys` and `Object.entries` must use the same order as JavaScript:
array-index names in ascending numeric order, followed by other names in
insertion order. An array-index name is a canonical decimal spelling below
2^32 - 1. Thus `01`, `-0` and `4294967295` are not array-index names.
The evaluator and the printed model share the ordering implementation.

The relevant operations are `OrdinaryGet` (ECMA-262 2024 §10.1.8.1),
`OrdinaryOwnPropertyKeys` (§10.1.11.1), and `Object.hasOwn`
(§20.1.2.13). The last operation requires ES2022.

## Implementation checkpoint

The supported certified subset is intentionally narrower than general
`Record<string, V>` indexing: direct guarded reads and locally guarded
callback and loop reads are accepted. Unguarded reads remain refused.
The generic type and own-key enumeration model remain available. This
checkpoint does not claim guards across bindings or an enclosing guard
as evidence for a callback or loop. Reduce callbacks remain outside the
ownership analysis.
