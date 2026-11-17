# Accept separate readonly declarations in error classes

The parser normalizes a separate readonly declaration and its constructor
assignment to the existing readonly parameter form. Each field must have
one required constructor parameter with the same name and primitive type.
The constructor must assign each declared field exactly once after
`super(message)`. The assignment must be unconditional and must read that
parameter directly.

This normalization keeps the error AST, evaluator and certificates unchanged.
The existing `program_sound` theorem covers the normalized program. The
parser's round-trip theorem still covers every accepted module. The source
printer writes parameter properties rather than separate declarations.

A plain parameter may be named `message`, `name`, `stack` or `cause`.
Only a field with one of those names could replace an inherited or own error
property, so the translator reserves those names for readonly parameters.

The constructor cannot observe the temporary undefined values of native
class fields. It calls `super` first, then only copies its parameters to the
declared fields. It cannot call a function, read `this`, branch, or write a
parameter between those assignments. The final message and field values
therefore agree with parameter properties.

Assignments from a differently named parameter or an expression remain
refused. The existing error AST records a field as a parameter, not an
initializer expression. Accepting those forms would require a larger model.
Optional fields, nonprimitive field annotations, initializers at declarations,
duplicate declarations, and repeated or missing assignments remain refused.

An assignment to `this.name` remains refused at this stage. The error class
tag identifies the constructor, but it does not represent the runtime `name`
property. A custom runtime name needs its own AST data and a proof through
the evaluator and generated certificates. Treating the constructor tag as
the runtime name would incorrectly change classes that inherit `"Error"`.

Per-file certificates for functions that return a custom thrown-error type
remain refused. The existing result encoder cannot encode that type:
certifying the new throwing example reports `cannot encode the result of check`.
The general `program_sound` theorem still covers these translations, and
the interpreter test compares the thrown message and fields with Node.
