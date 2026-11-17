# Object destructuring needs a binding operation

Object destructuring must evaluate its source once. For example,
`const { start, end } = makeSpan()` must not become two calls to
`makeSpan()`. The implementation should bind the result to a fresh internal
name, then read the fields in source order. A renamed binding such as
`{ start: first }` reads `start` and declares `first`.

The current syntax tree has an array binding pattern, but no object binding
pattern. Its evaluator and the `program_sound` proof likewise cover array
patterns only. Reusing array indexing would give object patterns the wrong
meaning. Introducing a block around separate declarations would also change
their scope. Neither shortcut is acceptable.

This change keeps object patterns refused and makes the diagnostic explain
the safe manual rewrite. It does not fix issue #261. Before accepting these
patterns, a follow-up must add their syntax tree, printer and parser proofs.
It must also extend the evaluator and the statement case of `program_sound`.
The parser comparison must compare object patterns with TypeScript's tree,
rather than hide them behind a lowered tree.

The first supported form should be a local `const` or `let` declaration with
identifier property names and optional renaming. Its source must be evaluated
once, and its bindings must belong to the surrounding block. The translator
must apply the existing restrictions on mutable aliases to the extracted
values. Tests must cover a call as the source, assignments to extracted `let`
bindings, renamed fields and collisions with generated names.

Nested patterns remain refused until the model accounts for each intermediate
property read. Defaults need conditional evaluation when a property is
undefined, so they remain refused too. Rest bindings need the semantics of
`CopyDataProperties`, including exclusions and enumeration order. Destructured
parameters need separate work on parameter binding and function entry.
Neither operation follows from array binding.

Object binding patterns date to ES2015, which specifies BindingInitialization
in §13.3.3.5 and KeyedBindingInitialization in §13.3.3.7. ES2024 specifies them
in §14.3.3.3 and §14.3.3.4. Every supported target has the basic operation.
Object rest first appeared in ES2018 and must not inherit that ES2015 boundary.
