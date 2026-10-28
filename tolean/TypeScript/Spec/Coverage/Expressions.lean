import tolean.TypeScript.Spec.Eval

/-! # §13 ECMAScript Language: Expressions {#sec-ecmascript-language-expressions} -/
namespace tolean.TypeScript.Coverage

open tolean.TypeScript tolean.TypeScript.Syntax
open tolean.TypeScript.Eval (Val)

/-! ### §13.2.5.5 Runtime Semantics: PropertyDefinitionEvaluation {#sec-runtime-semantics-propertydefinitionevaluation} -/

/-- `{ NaN }` reads the global `NaN` when no local hides it, as any
`IdentifierReference` does. The interpreter once looked the name up only
among the locals, and gave no value. -/
theorem shorthand_reads_global {N : Type} [JSNumber N] (m : Eval.Scope) (fuel : Nat) (sp : Span) :
    Eval.eval (N := N) m fuel [] (.object sp [.shorthand sp "NaN"]) =
      some (.obj [("NaN", .num JSNumber.nan)]) := by
  simp [Eval.eval, Eval.evalProps, List.lookup]

/-! ### §13.5.5 Unary - Operator {#sec-unary-minus-operator} -/

/-- `-Infinity` negates a local named `Infinity` as it negates any value, a
bigint too. The interpreter once gave no value when the local held a
bigint. -/
theorem neg_local_infinity {N : Type} [JSNumber N] (m : Eval.Scope) (fuel : Nat) (sp : Span) (i : Int) :
    Eval.eval (N := N) m fuel [("Infinity", .int i)] (.unary sp .neg (.ident sp "Infinity")) =
      some (.int (-i)) := by
  simp [Eval.eval, List.lookup]

end tolean.TypeScript.Coverage
