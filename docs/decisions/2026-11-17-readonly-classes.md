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

The pass preserves class-instance provenance before it erases methods. A
class-typed local or result must use a direct `new C` expression. A plain
object, a function result, or a spread copy cannot acquire class provenance
from its annotation. A type alias to a class keeps that identity when the pass
checks calls and spreads. Source functions, methods, and constructors cannot
accept class-typed parameters, because callers could supply an object with
matching fields but no class prototype.

An inferred receiver with a known non-class type keeps its normal operation.
For example, `Map.get` remains valid when an unrelated class also declares a
`get` method. An unknown or possibly class-typed receiver still cannot use
static class dispatch.

## What is proved

The ordinary-class parser has separate token round-trip theorems for fields,
constructors, methods, the member loop and class declarations. The parser
well-formedness proof and source-text round trip include ordinary classes.
The old error-class parser and its reading theorem remain separate.

The existing `program_sound_call` theorem still relates the interpreter and
the IR on the **elaborated module**. Its value relation is unchanged.
Certificates retain the original parsed tree and prove, by kernel reduction
split into source-hygiene and structural elaboration steps, that the pass
produces the literal lowered module used in the translation theorem. This
establishes which tree the pass produces. It is not a proof that elaboration
preserves the semantics of the original class program.

The certificate chain records these as separate facts. It keeps the structural
`program_elaborated` theorem, then records the semantic-preservation boundary
as tested against Node. The translator stays tested rather than proved for a
class-bearing file.

## What Node checks

`tests/typescript/interpreter.test.ts` runs original class programs in Node and
compares their results with interpretation after elaboration. Cases cover
construction, inferred local receiver types, explicit receiver annotations,
method calls on `this`, constructor assignment order, parameter properties,
class results passed through annotated functions, rejection of plain objects
and copies, object destructuring of class fields, and unrelated `Map.get`
dispatch. These comparisons test the
semantic boundary that the Lean theorem does not yet prove. They do not
establish semantic preservation for every accepted program.

## Refusals

The pass refuses inheritance, mutable or optional fields, field initializers,
accessors, static members, generic classes, arbitrary constructor statements,
duplicate assignments, extracted methods, computed class properties,
`instanceof`, constructor identity and constructor-property reads. It refuses
bare `this`, including a return of it or an argument that passes it out.
An arrow may read a field through lexical `this`; a nested ordinary function
cannot borrow the enclosing method's receiver.
It also refuses class-typed source parameters, nested class values in
containers, and class-typed locals that do not use a direct constructor
expression. Object destructuring may read a class instance's readonly fields,
but each destructured name has no class type. The existing type checks still
refuse uses that require a class method, including calls through a destructured
name.

The remaining translator checks still apply after elaboration. In particular,
this work does not introduce mutable object aliases, prototype mutation,
reflection, dynamic dispatch or arbitrary JavaScript interoperation.

Ordinary field declarations require ES2022. `Edition.lean` records the class,
field-initialization and construction operations. Earlier targets refuse the
ordinary-class parser rather than silently downlevel the original source.
