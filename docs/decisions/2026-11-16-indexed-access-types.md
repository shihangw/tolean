# Resolve literal-key indexed access types statically

Issue #263 asks for `T['field']` to reuse the type of a declared field.
This is a type annotation, not a runtime property read. We resolve it to the
field's translated type without adding an expression to the output.

## Syntax and proofs

`TypeExpr.indexed` records the receiver and a literal string key. The parser
reads nonempty type brackets as an indexed access and retains empty brackets
for array types. The source printer preserves both forms.

The previous round-trip proof decomposed a postfix type into a primary type
and a count of array suffixes. That statement cannot describe indexed
access. The new decomposition records each suffix as either an array suffix
or a string key. The loop proof follows that list. The parser's
well-formedness and token-skeleton proofs cover the additional branch.
Their claims still apply to every accepted source program.

## Static lookup

The translator resolves the receiver through the existing type translator.
It then requires a structure and finds the key in its instantiated fields.
This preserves named literal-union identity, generic field substitution and
the optionality of optional fields. It also handles imported interfaces and
aliases through their existing declaration references.

A nested indexed access repeats this operation. A union receiver, an
unconstrained generic receiver or an optional or nullable intermediate
receiver does not resolve to a structure, so the translator refuses it.
A missing key fails explicitly. Unions of keys, `keyof` and numeric keys
remain refused because the parser accepts only one literal string key.

The exact example in #263 also requires an anonymous union of string literals
in an interface field. That remains refused. Such a union needs a generated
inductive type and rules for its identity across declarations and imported
modules. This is a separate extension, not a field lookup. Declaring
`type Kind = 'circle' | 'square'` and using `Kind` in the field makes the
indexed parameter annotation work.

## Runtime meaning and validation

TypeScript introduced indexed access types in version 2.1. The TypeScript
Handbook describes them under “Indexed Access Types.” They erase before
execution and add no ECMAScript edition gate. The example's property read
uses OrdinaryGet (ES2024 section 10.1.8.1), and its comparison uses
IsStrictlyEqual (section 7.2.15). Both operations exist in ES2015, the oldest
supported target. `Edition.lean` records these references.

The evaluator does not change. `program_sound` covers the translator's
resolved field types through its existing claim for translated programs.
The certifier serializes the new source constructor without changing the
meaning of certificates.

Parser fixtures cover the original example and nested suffixes. Translation
fixtures cover aliases, nested access, missing fields and generic receiver
refusal. A project fixture covers imports and optional fields. The
interpreter test compares the named-literal-union example with Node.
