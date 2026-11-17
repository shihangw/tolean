# Keep ordinary classes refused

**Status:** decided, not implemented · **Date:** 2026-11-17

Step 13 of the [pure TypeScript plan](../plans/pure-typescript.md) proposed
translating classes with readonly fields and methods that do not change
`this` into a structure and one Lean function per method. Tolean will not use
that translation yet. It continues to accept only the separate, existing
`extends Error` subset.

An ordinary class declaration creates a runtime constructor and a prototype.
Constructing an instance, reading a field, and calling a method therefore
involve more than the field values. A structure plus free functions would
change observable behavior when code tests constructor identity, uses
`instanceof`, reads or shadows a method, or passes an instance to JavaScript
that inspects its prototype. Readonly fields prevent writes through TypeScript
types; they do not remove these runtime observations.

The current interpreter represents ordinary objects as property lists. It
does not model a class constructor, prototype lookup, or method receiver.
The current intermediate representation and its soundness theorem therefore
cannot certify those observations. Treating a class as an interface would
skip the constructor and method behavior rather than prove it equivalent.

The translator will keep refusing ordinary classes until the evaluator and
intermediate representation model the runtime behavior needed by an accepted
subset, or until the translator proves that a particular use cannot observe
the difference. Mutable fields and methods that change `this` remain refused
even after that work: they need an explicit account of aliasing and mutation.
Getters, setters, inheritance other than from `Error`, and static state also
remain refused.

This decision adds no TypeScript construct, so it adds no edition entry.
