# Keep indexed access types refused until their source proofs are extended

Issue #263 asks for `T['field']` to reuse the type of a declared field.
This is a type annotation, not a runtime property read. It should resolve
to the field's translated type without adding an expression to the output.

The current implementation cannot express that syntax in `TypeExpr`.
The parser's `arrayStep` accepts only an empty pair of brackets. Its
`arrayStep_inv` and `arrayStep_skel` proofs describe precisely that behavior.
Accepting a nonempty pair requires a new source constructor and corresponding
changes to the printer, source well-formedness proofs and round-trip proofs.
Encoding an indexed access as a fabricated type reference would not preserve
the source syntax and is not an acceptable shortcut.

The reported example also needs support for an anonymous union of string
literals in an interface field. `translateType` currently refuses such a
union because the output needs a named inductive type. Resolving the indexed
access alone would therefore not make the reported example translate.

This change records the refusal boundary and a supported workaround. It does
not implement indexed access types or close the implementation gap in #263.
The parser, translator, evaluator and certifier remain unchanged, so their
existing proofs retain their statements.

## Intended implementation

A future implementation should add a source constructor that holds the
receiver type and a literal string key. It should resolve the receiver to a
declared or imported structure, look up the field and return its existing
translated type. It must preserve the identity of named literal unions and
the optionality of optional fields. A nested access can repeat that operation
only when the intermediate type resolves to a structure.

The first implementation should refuse unions of keys, `keyof`, numeric keys
and unresolved generic receivers. Those forms require more than one known
field lookup. Missing fields must fail rather than acquire an assumed type.
Receiver unions and nullable or optional intermediate receivers also need
explicit rules before they can be accepted.

Anonymous literal unions need a separate decision about generated names and
their identity across imported modules. Until that is implemented, callers
can declare a named literal union and use it for both the field and the
parameter.

## Runtime meaning and validation

TypeScript introduced indexed access types in version 2.1. The TypeScript
Handbook describes them under “Indexed Access Types.” They erase before
execution and add no ECMAScript edition gate. The example's property read
uses OrdinaryGet (ES2024 section 10.1.8.1), and its comparison uses
IsStrictlyEqual (section 7.2.15). Both operations exist in ES2015, the oldest
supported target.

Before accepting the syntax, the implementation must extend the source
proofs without weakening their claims. It must also establish that
`program_sound` covers the resolved field types, record the edition and
specification references in `Edition.lean`, and compare indexed-access
programs with Node in `interpreter.test.ts`. The certificate corpus must
pass if the certifier or evaluator changes.

The regression fixtures in this change keep literal keys, nested access,
key unions, `keyof`, numeric keys and generic receivers explicitly refused.
They do not assert that these valid TypeScript programs are invalid.
