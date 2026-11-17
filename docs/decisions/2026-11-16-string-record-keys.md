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

A dictionary lookup needs the condition that the key is own or is not a
name on `Object.prototype`. Otherwise JavaScript can return an inherited
function rather than a value of type `V`. The source evaluator and the IR
evaluator already return no result for an absent inherited name.

Functions with an unguarded dynamic lookup receive a conditional printer
link. Its premise says that the IR run on the encoded inputs returns a
result. The final certificate takes that same premise and applies the
existing `decls_sound` theorem. No converse compiler theorem or new
`program_sound` premise is needed.

`getKey_success_iff` states the local condition precisely.
`getKey_encRecord_of_success` relates a successful evaluator lookup to the
total Option lookup in the printed model. In an otherwise total certified
function, the new premise therefore excludes exactly the absent inherited
lookup case. It applies to the actual run, not just the initial arguments.

Certificates for functions without these lookups retain their existing
unconditional statements and proof text. The intended guarded forms are
`if (Object.hasOwn(record, key))` and iteration over the record's own keys
or entries. These forms need no extra premise when the certificate
generator can recognize the ownership evidence.

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

The first runtime checkpoint accepts named and inline dictionaries,
identifier-keyed literals, and dynamic indexing. Its translator and
certificate generator compile, and the generated dictionary definitions
compile. It also supplies the own-key model and the lookup lemmas.

This checkpoint is not the completed feature. Object-operation dispatch,
guarded and iteration certificate proofs, quoted literal keys, and the
full certificate and Node comparisons still need validation. The draft
pull request must remain a draft until those checks pass.
