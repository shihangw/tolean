# Object patterns bind fields from one source value

Local `const` and `let` declarations accept flat object patterns with
identifier keys and optional renaming. The syntax tree retains the pattern.
Its printer preserves shorthand and renamed properties, and the parser
comparison checks those properties against TypeScript's binding tree.

The output evaluates the source once. A structure-pattern expression selects
the fields and returns their values as a tuple. The existing tuple binding
then declares the user's names in the surrounding scope. The structure
pattern includes `..`, so a declaration need not name every field. Repeated
property keys share one pattern field, but each requested local receives its
value. Generated names stay inside the expression and cannot capture the
source or leak into the continuation.

An output-only temporary was not a direct fit for the existing proof.
`Agree` compares every name in the source and output environments, so a
private binding in just the output breaks its continuation hypothesis.
The structure-pattern expression avoids that mismatch without changing
`Agree`. Its evaluator extracts fields from one object value, and the
statement proof uses the existing `binds_sim` and tuple-binding argument.
The source evaluator reads the same fields in source order.

Renaming is by property name, not position. For example, `{ a: b, b: a }`
reads `a` into `b` and `b` into `a`. But `{ a: s, b } = s` does not read an
outer `s`: JavaScript resolves the initializer to the new local `s` and
throws because it is not initialized yet. The translator refuses a source
that mentions one of the pattern's binding names. The interpreter gives no
value for that form, rather than incorrectly reading the outer binding.

The existing restrictions on aliases still apply to extracted collections.
Nested patterns, defaults, rest elements and computed keys remain refused.
Empty patterns, exported patterns and patterns in loop heads remain refused
too. Destructured parameters need separate work on function entry and
parameter binding, so they remain refused.

Object binding patterns date to ES2015, which specifies
BindingInitialization in §13.3.3.5 and KeyedBindingInitialization in
§13.3.3.7. ES2024 specifies them in §14.3.3.3 and §14.3.3.4. Every supported
target has these operations. Object rest first appeared in ES2018 and does
not inherit the ES2015 boundary.
