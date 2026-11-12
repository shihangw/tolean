# The errors of a file are one inductive type of that file

Decided on 2026-11-11, with the pull request that translates error classes.

## Question

Which type should a translated function throw once the program declares
error classes? `JSError` holds only a message. A class with fields needs a
sum of the error classes, and a call can reach a class of another file.

## Decision

Each file that declares error classes gets one inductive type, `Thrown`,
at the top of its output. `Thrown.error` holds a `JSError`, for
`throw new Error(m)`, and each class has a constructor with the message
and its `readonly` fields. Every function of the file that can throw
returns `Except Thrown R`. A file with no error classes keeps `JSError`, so
the output of code that was in the subset before does not change.

A call of a function of another file that can throw is accepted only when
neither file declares error classes. Otherwise the two files throw values
of two types, and `>>=` cannot pass one on as the other.

## Why

The plan recommended one inductive type for the whole program, generated as
`Errors.lean`, so that a callee's error passes through `>>=` across files
without a conversion. That type needs every file's classes before any file
translates, and the soundness proof would have to relate the program-wide
type to each file's translation. One type per file needs neither: the
translator reads the classes from the file it translates, and the proof
relates the file's own declarations, as it does for its interfaces and
unions.

The cost is the cross-file rule above. The survey found no program that
throws a class across files, so the rule costs nothing yet. When one
appears, a program-wide type can replace the per-file one, and this record
should then be superseded.

## Consequences

- `Thrown` comes before every other declaration of the file, so its
  constructors may name only `JSError` and primitive types. A parameter of
  an error class must be a `bigint`, a `number`, a `boolean` or a `string`.
- An error class must be declared before the functions that throw it, as
  in JS, which does not hoist a class.
- The interpreter and the translator rewrite `throw new C(args)` to
  `throw new C(message, args)` before they run or translate a body, with the
  constructor's message written over the arguments, which have moved to
  names first. So the statement that makes the error needs no scope of its
  own, and the two sides agree on what they rewrite.
