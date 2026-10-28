import tolean.TypeScript.Spec.Conformance.LexicalGrammar
import tolean.TypeScript.Spec.Conformance.Expressions
import tolean.TypeScript.Spec.Conformance.Statements
import tolean.TypeScript.Spec.Conformance.Modules

/-!
Checks that the interpreter and the translator follow ECMA-262. There is one
file for each chapter, and this list is in the order of the chapters:

- `LexicalGrammar`: chapter 12, ECMAScript Language: Lexical Grammar.
- `Expressions`: chapter 13, ECMAScript Language: Expressions.
- `Statements`: chapter 14, ECMAScript Language: Statements and Declarations.
- `Modules`: chapter 16, ECMAScript Language: Scripts and Modules.

Each check covers a rule that the interpreter or the translator once broke.
A theorem states the rule for every input. A `#guard` checks one input, where
the rule is about concrete strings. CI builds these files with the rest of
the library, so a check that stops holding fails the build.

The section numbers are those of ES2024, the default target. Each check also
names the production or the operation, because section numbers move between
editions. The rules that come from Lean and the project, and not from
ECMA-262, are in `Proof/Output.lean`.
-/
