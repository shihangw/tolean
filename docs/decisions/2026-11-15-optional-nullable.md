# Keep null and undefined distinct

An optional nullable value has type `JSNullish T` in Lean. This is an
abbreviation for `Option (Option T)`. Its three named cases are
`JSNullish.undefined`, `JSNullish.null`, and `JSNullish.value x`.
They abbreviate `none`, `some none`, and `some (some x)`, respectively.
The printer uses the qualified names in values and patterns, so readers
need not remember which option layer represents null. An omitted optional
argument or field reads as `undefined`. Neither nullish value is confined
to JavaScript.

ECMA-262 defines Null and Undefined as separate types (§6.1.2 and §6.1.3
in ES2024). Strict equality distinguishes them (§7.2.15), while loose
equality compares them equal (§7.2.14). Nullish coalescing (§13.13.1) and
optional chaining (§13.3.9) treat both as absent. The interpreter already
has separate `Val.null` and `Val.undefined` constructors. Collapsing them
would change the meaning of strict comparisons, not merely the output type.

Nested options preserve the existing types for nullable and optional values.
A dedicated three-case inductive would make case analysis more explicit,
but it would need new conversions wherever a value changes from nullable
to optional nullable. Nested options use Lean's existing constructors and
lemmas instead. Coalescing must inspect both layers. Optional chaining
must skip its projection for either nullish value, but preserve a null
that the projected field holds. Narrowing against undefined removes only
the outer layer.

An object without a key is still not the same object as one whose key
holds undefined. The nested option models the value of a field read, not
that distinction between objects. Explicit undefined object fields and
presence-sensitive operations remain refused. In particular, this design
does not license `in`, object key enumeration, or object JSON serialization.
JSON serialization keeps null fields but drops undefined fields.

Go and SQL are separate source-language frontends, not TypeScript output
backends. This decision changes only the TypeScript frontend. It adds no
Go or SQL type and does not change either frontend's behavior.
