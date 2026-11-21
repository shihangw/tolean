# Accept separate readonly declarations in error classes

The parser normalizes a separate readonly declaration and its constructor
assignment to the existing readonly parameter form. Each field must have
one required constructor parameter with the same name and primitive type.
The constructor must assign each declared field exactly once after
`super(message)`. The assignment must be unconditional and must read that
parameter directly.

The parser refuses a normalization that would reorder own fields. TypeScript
creates parameter properties in parameter order before separate declarations
in declaration order. The normalized readonly parameters must have exactly
that order. Assignments must also follow declaration order because TypeScript
downlevel output creates separately declared fields when it assigns them.
These checks preserve enumeration order on both native and downlevel classes.
The interpreter tests compare complete thrown values without sorting fields.

This normalization keeps the error AST, evaluator and certificates unchanged.
The existing `program_sound` theorem covers the normalized program. The
parser's round-trip theorem still covers every accepted module. The source
printer writes parameter properties rather than separate declarations.

A plain parameter may be named `message`, `name`, `stack` or `cause`.
Only a field with one of those names could replace an inherited or own error
property, so the translator reserves those names for readonly parameters.

Both readonly parameter properties and separate readonly declarations refuse
`__proto__` fields. Downlevel assignment invokes the inherited prototype setter,
which ignores primitive values rather than creating an own field. Native field
definitions create that field instead. We refuse this name rather than model
assignment and definition separately. A plain `__proto__` parameter remains
legal because it does not write a field. The shared translator check applies
after the parser normalizes separate declarations.

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

The follow-up accepts one unconditional string-literal assignment to
`this.name` after `super`. The constructor AST records the optional literal
separately from its parameters and message. ClassInfo carries it through
translation, and the generated error constructor stores the explicit name
as a string field. The evaluator appends that own property to the other
fields. The constructor tag still identifies the class, even when its
runtime name differs. An instance with no own name inherits `"Error"`.

The name comes after the other fields in the model. ES2022 native class
initialization creates declared fields before execution resumes after
`super`, so an assignment to `this.name` may precede or follow their
assignments. Before ES2022, the parser requires the name assignment after
all separate field assignments. Otherwise downlevel TypeScript output would
create the name first and change the own-property order. Parameter properties
already exist before either kind of assignment. The interpreter tests compare
complete errors at both targets without sorting their fields.

Repeated name assignments, computed names, bracket notation, and conditional
assignments remain refused. Names may be empty, contain Unicode, or differ
from the class name. Optional chaining on an error and constructing an error
outside a throw remain outside the translated subset.

Per-file certificates for functions that return a custom thrown-error type
remain refused. The existing result encoder cannot encode that type:
certifying the new throwing example reports `cannot encode the result of check`.
The general `program_sound` theorem still covers these translations, and
the interpreter test compares the thrown message and fields with Node.
