import tolean.TypeScript.Proof.Expr

/-! # §14 ECMAScript Language: Statements and Declarations {#sec-ecmascript-language-statements-and-declarations} -/
namespace tolean.TypeScript.Coverage

open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate tolean.TypeScript.Proof

/-! ### §14.3.1 Let and Const Declarations {#sec-let-and-const-declarations}

A `let` or `const` variable exists from the start of its block, but it "may
not be accessed in any way until the variable's LexicalBinding is
evaluated". A read before that throws (`GetBindingValue`, §9.1.1.1.6). -/

/-- A local never has the name of a function that a call may name, or of a
global that the subset reads. So the subset never reads such a name as the
function or the global where JS reads the local before its declaration, and
throws. -/
theorem declare_not_callable {env env' : Translate.Env} {sp : Span} {name : String} {b : Binding}
    {t : Ty} {s s' : Ctx} (h : declare env sp name b t s = .ok env' s') :
    (∀ f ∈ env.functions, f.name ≠ name) ∧ name ≠ "NaN" ∧ name ≠ "Infinity" ∧ name ≠ "Number" := by
  simp only [declare, ite_state] at h
  split at h
  · simp at h
  · simp only [pure_bind, ite_state] at h
    split at h
    · simp at h
    · rename_i hg
      refine ⟨fun f hf hn => hg ?_, ?_, ?_, ?_⟩
      · simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
        exact Or.inl ⟨f, hf, hn⟩
      all_goals rintro rfl; simp [isNumberName] at hg

end tolean.TypeScript.Coverage
