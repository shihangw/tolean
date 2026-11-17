# Elaborate readonly classes before evaluation

**Status:** implemented, validation in progress · **Date:** 2026-11-17

Ordinary classes use static dispatch in the accepted slice. Tolean elaborates
them before both interpretation and IR translation. It does not add a runtime
class tag or change `Eval.Val`. The existing `extends Error` parser remains
separate.

Each class becomes an interface of its readonly fields. Its constructor
becomes a free function that returns an object literal. Each method becomes a
free function whose first parameter holds the receiver. `new C(args)` calls
the constructor function. A method call passes its receiver once, followed by
its arguments, to the method function.

The constructor assigns each declared field once. Its right-hand sides become
local bindings in assignment order, so elaboration does not reorder their
evaluation. The final object lists its fields in declaration order. Readonly
parameter properties precede declared fields, as TypeScript emits them.
Generated names use a reserved prefix that the source cannot bind.

Dispatch requires the receiver's declared or inferred type to be exactly the
class. A union, `any`, an unresolved alias, or an unknown type cannot select a
method. The pass tracks parameter annotations, local annotations, constructor
results, annotated function and method results, and class field types. It
does not claim to implement TypeScript's full type inference.

## What is proved

The ordinary-class parser has separate token round-trip theorems for fields,
constructors, methods, the member loop and class declarations. The parser
well-formedness proof and source-text round trip include ordinary classes.
The old error-class parser and its reading theorem remain separate.

The existing `program_sound_call` theorem still relates the interpreter and
the IR on the **elaborated module**. Its value relation is unchanged.
Certificates retain the original parsed tree. A compiled `#guard` checks the
elaboration result before the certificate proves translation of the lowered
tree. That guard is not a kernel theorem. Nor is it a proof that the pass
preserves the semantics of the original class program.

A kernel-checked elaboration equation was attempted on the class fixture.
`decide +kernel` did not reduce its Boolean check to a decision, and
`#reduce` exceeded a recursion depth of 10,000. The compiled check returns
`true` for that fixture. This narrows only the certificate's extra elaboration
check, not the accepted class slice or the existing translation theorem.

## What Node checks

`tests/typescript/interpreter.test.ts` runs original class programs in Node and
compares their results with interpretation after elaboration. Cases cover
construction, inferred local receiver types, explicit receiver annotations,
method calls on `this`, constructor assignment order, parameter properties,
and class results passed through annotated functions. These comparisons test
the semantic boundary that the Lean theorem does not yet prove. They do not
establish semantic preservation for every accepted program.

## Refusals

The pass refuses inheritance, mutable or optional fields, field initializers,
accessors, static members, generic classes, arbitrary constructor statements,
duplicate assignments, extracted methods, computed class properties,
`instanceof`, constructor identity and constructor-property reads. It refuses
bare `this`, including a return of it or an argument that passes it out.
An arrow may read a field through lexical `this`; a nested ordinary function
cannot borrow the enclosing method's receiver.

The remaining translator checks still apply after elaboration. In particular,
this work does not introduce mutable object aliases, prototype mutation,
reflection, dynamic dispatch or arbitrary JavaScript interoperation.

Ordinary field declarations require ES2022. `Edition.lean` records the class,
field-initialization and construction operations. Earlier targets refuse the
ordinary-class parser rather than silently downlevel the original source.
