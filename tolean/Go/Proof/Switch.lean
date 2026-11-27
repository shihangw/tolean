import tolean.Go.Translate.Pure

/-!
An `if` with an init statement and an expression switch mean, in the
interpreter, what the statements that the translator writes for them mean.

The translator writes `if s; c { … }` as the block `{ s; if c { … } }`, and a
switch as a chain of `if` statements, in a block after its init statement
when it has one. The theorems here show that the interpreter gives each
rewritten statement the outcome that it gives the original, in every
environment. So `Proof/Stmt.lean` proves the rewritten statement, and the
proof carries over.
-/
namespace tolean.Go.Proof

open tolean.Go tolean.Go.Syntax tolean.Go.Pure
open tolean.Go.Eval (Val Outcome)

variable (p : Eval.Program) (fuel : Nat)

/-- The end of an implicit block: a return passes, and the names that the
block declared go out of scope. -/
def leave (ρ : Eval.Env) : Outcome → Outcome
  | .ret v => .ret v
  | .normal ρ' => .normal (ρ'.drop (ρ'.length - ρ.length))

theorem leave_leave (ρ : Eval.Env) (o : Outcome) : leave ρ (leave ρ o) = leave ρ o := by
  cases o with
  | ret v => rfl
  | normal ρ' =>
    simp only [leave, List.length_drop, Outcome.normal.injEq]
    have : ρ'.length - (ρ'.length - ρ.length) - ρ.length = 0 := by omega
    rw [this, List.drop_zero]

theorem leave_self (ρ : Eval.Env) : leave ρ (.normal ρ) = .normal ρ := by
  simp [leave]

theorem bind_leave (x : Option Outcome) (ρ : Eval.Env) :
    (x.bind fun
      | .ret v => some (.ret v)
      | .normal ρ' => some (.normal (ρ'.drop (ρ'.length - ρ.length)))) = x.map (leave ρ) := by
  cases x with
  | none => rfl
  | some o => cases o <;> rfl

theorem block_eq (sp : Span) (body : List Stmt) (ρ : Eval.Env) :
    Eval.execStmt p fuel ρ (.block sp body) = (Eval.exec p fuel ρ body).map (leave ρ) := by
  rw [Eval.execStmt, ← bind_leave]; rfl

theorem exec_cons_eq (s : Stmt) (rest : List Stmt) (ρ : Eval.Env) :
    Eval.exec p fuel ρ (s :: rest) = (Eval.execStmt p fuel ρ s).bind fun
      | .ret v => some (.ret v)
      | .normal ρ' => Eval.exec p fuel ρ' rest := by
  rw [Eval.exec]; rfl

theorem exec_nil_eq (ρ : Eval.Env) : Eval.exec p fuel ρ [] = some (.normal ρ) := by
  rw [Eval.exec]

/-- Two statements that the interpreter gives the same outcome, in every
environment, can stand for each other at the head of a list. -/
theorem exec_cons_congr {a b : Stmt} (h : ∀ ρ, Eval.execStmt p fuel ρ a = Eval.execStmt p fuel ρ b)
    (rest : List Stmt) (ρ : Eval.Env) : Eval.exec p fuel ρ (a :: rest) = Eval.exec p fuel ρ (b :: rest) := by
  rw [exec_cons_eq, exec_cons_eq, h]

theorem execStmt_ifInit (sp : Span) (s : Stmt) (c : Expr) (t : Stmt) (els : Option Stmt) (ρ : Eval.Env) :
    Eval.execStmt p fuel ρ (.ifStmt sp (some s) c t els) =
      Eval.execStmt p fuel ρ (.block sp [s, .ifStmt sp none c t els]) := by
  rw [block_eq, exec_cons_eq, Eval.execStmt]
  cases h : Eval.execStmt p fuel ρ s with
  | none => simp
  | some o =>
    cases o with
    | ret v => simp [leave]
    | normal ρ₁ =>
      simp only [Option.bind_some, exec_cons_eq, exec_nil_eq]
      cases h2 : Eval.execStmt p fuel ρ₁ (.ifStmt sp none c t els) with
      | none => simp [h2]
      | some o => cases o <;> simp [h2, leave]

theorem execStmt_switchInit (sp : Span) (s : Stmt) (tag : Option Expr) (bsp : Span)
    (cs : List CaseClause) (ρ : Eval.Env) :
    Eval.execStmt p fuel ρ (.switchStmt sp (some s) tag bsp cs) =
      Eval.execStmt p fuel ρ (.block bsp [s, .switchStmt sp none tag bsp cs]) := by
  rw [block_eq, exec_cons_eq, Eval.execStmt]
  cases h : Eval.execStmt p fuel ρ s with
  | none => simp
  | some o =>
    cases o with
    | ret v => simp [leave]
    | normal ρ₁ =>
      simp only [Option.bind_some, exec_cons_eq, exec_nil_eq]
      cases h2 : Eval.execStmt p fuel ρ₁ (.switchStmt sp none tag bsp cs) with
      | none => simp [h2]
      | some o => cases o <;> simp [h2, leave]

/-! ### Case tests -/

/-- The boolean of a value. -/
def asBool : Val → Option Bool
  | .bool b => some b
  | _ => none

/-- The switch expression `tag` has the value `v`, and a missing one is
`true`. -/
def TagVal (ρ : Eval.Env) : Option Expr → Val → Prop
  | none, v => v = .bool true
  | some x, v => Eval.eval p fuel ρ x = some v

theorem caseTest_eval {ρ : Eval.Env} {tag : Option Expr} {v : Val} (ht : TagVal p fuel ρ tag v)
    (sp : Span) (e : Expr) :
    (Eval.eval p fuel ρ (caseTest sp tag e)).bind asBool =
      (Eval.eval p fuel ρ e).bind (Eval.eqVal v) := by
  cases tag with
  | none =>
    simp only [TagVal] at ht
    subst ht
    simp only [caseTest]
    cases Eval.eval p fuel ρ e with
    | none => rfl
    | some w => cases w <;> simp [asBool, Eval.eqVal]
  | some x =>
    simp only [TagVal] at ht
    simp only [caseTest]
    rw [Eval.eval]
    simp only [Eval.BinOp.ofString?, ht]
    cases Eval.eval p fuel ρ e with
    | none => rfl
    | some w =>
      cases h : Eval.eqVal v w <;> simp [Eval.binary, h, asBool]

theorem caseCond_none {sp : Span} {tag : Option Expr} {es : List Expr} (h : caseCond sp tag es = none) :
    es = [] := by
  cases es with
  | nil => rfl
  | cons e es =>
    simp only [caseCond] at h
    split at h <;> simp at h

theorem caseCond_eval {ρ : Eval.Env} {tag : Option Expr} {v : Val} (ht : TagVal p fuel ρ tag v) (sp : Span) :
    ∀ {es : List Expr} {c : Expr}, caseCond sp tag es = some c →
      (Eval.eval p fuel ρ c).bind asBool = Eval.matchAny p fuel ρ v es
  | [], c, h => by simp [caseCond] at h
  | e :: es, c, h => by
    rw [Eval.matchAny]
    simp only [caseCond] at h
    split at h
    · next hn =>
      simp only [Option.some.injEq] at h
      subst h
      rw [caseCond_none hn, caseTest_eval p fuel ht sp e]
      cases Eval.eval p fuel ρ e with
      | none => rfl
      | some w =>
        cases h : Eval.eqVal v w with
        | none => simp only [Option.bind_some, Option.bind_eq_bind, h]; rfl
        | some b => cases b <;> simp [h, Eval.matchAny]
    · next r hr =>
      simp only [Option.some.injEq] at h
      subst h
      have ih := caseCond_eval ht sp hr
      have ht' := caseTest_eval p fuel ht sp e
      rw [Eval.eval]
      simp only [Eval.BinOp.ofString?]
      cases hl : Eval.eval p fuel ρ (caseTest sp tag e) with
      | none =>
        rw [hl] at ht'
        cases he : Eval.eval p fuel ρ e with
        | none => rfl
        | some w =>
          rw [he] at ht'
          simp only [Option.bind_none, Option.bind_some] at ht'
          simp [← ht']
      | some lv =>
        rw [hl] at ht'
        cases lv with
        | bool x =>
          cases he : Eval.eval p fuel ρ e with
          | none => simp [he, asBool] at ht'
          | some w =>
            rw [he] at ht'
            simp only [Option.bind_some, asBool] at ht'
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, ← ht']
            cases x with
            | true => simp [asBool]
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [← ih]
              cases Eval.eval p fuel ρ r with
              | none => rfl
              | some rv => cases rv <;> simp [asBool]
        | int i | str s =>
          cases he : Eval.eval p fuel ρ e with
          | none => simp [he, asBool] at ht' ⊢
          | some w =>
            rw [he] at ht'
            simp only [Option.bind_some, asBool] at ht'
            simp [← ht']

/-! ### The chain of `if` statements -/

theorem execStmt_if_eq (sp : Span) (c : Expr) (t : Stmt) (els : Option Stmt) (ρ : Eval.Env) :
    Eval.execStmt p fuel ρ (.ifStmt sp none c t els) =
      ((Eval.eval p fuel ρ c).bind asBool).bind fun b =>
        (if b then Eval.execStmt p fuel ρ t
          else match els with
            | some f => Eval.execStmt p fuel ρ f
            | none => some (.normal ρ)).map (leave ρ) := by
  rw [Eval.execStmt]
  cases Eval.eval p fuel ρ c with
  | none => rfl
  | some w =>
    cases w with
    | bool b =>
      simp only [Option.bind_some, asBool]
      rw [← bind_leave]
      cases b
      · cases els <;> rfl
      · rfl
    | int i => rfl
    | str s => rfl

theorem matchAny_nil (ρ : Eval.Env) (v : Val) : Eval.matchAny p fuel ρ v [] = some false := by
  rw [Eval.matchAny]

/-- The clauses mean what their chain means, once the switch expression has
the value `v`. -/
theorem chain_eval {ρ : Eval.Env} {tag : Option Expr} {v : Val} (ht : TagVal p fuel ρ tag v) :
    ∀ (cs : List CaseClause) (dflt : Option (Span × List Stmt)),
      (Eval.execClauses p fuel ρ v cs (dflt.map (·.2))).map (leave ρ) =
        match switchChain tag dflt cs with
        | none => some (.normal ρ)
        | some d => Eval.execStmt p fuel ρ d
  | [], none => by
    rw [Eval.execClauses.eq_def]; simp [switchChain, leave_self]
  | [], some (sp, body) => by
    rw [Eval.execClauses.eq_def]; simp [switchChain, block_eq]
  | .mk sp none body :: rest, dflt => by
    rw [Eval.execClauses.eq_def]
    simp only [switchChain]
    exact chain_eval ht rest (some (sp, body))
  | .mk sp (some es) body :: rest, dflt => by
    rw [Eval.execClauses.eq_def]
    simp only [switchChain]
    cases hc : caseCond sp tag es with
    | none =>
      rw [caseCond_none hc, matchAny_nil]
      exact chain_eval ht rest dflt
    | some c =>
      simp only
      rw [execStmt_if_eq, caseCond_eval p fuel ht sp hc]
      have ih := chain_eval ht rest dflt
      cases Eval.matchAny p fuel ρ v es with
      | none => rfl
      | some b =>
        cases b with
        | true =>
          simp only [Option.bind_some, ↓reduceIte, block_eq, Option.map_map]
          congr 1; funext o; exact (leave_leave ρ o).symm
        | false =>
          simp only [Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true, ↓reduceIte]
          cases hch : switchChain tag dflt rest with
          | none => simp only [hch] at ih; rw [ih]; simp [leave_self]
          | some f =>
            simp only [hch] at ih
            simp only
            rw [← ih, Option.map_map]
            congr 1; funext o; exact (leave_leave ρ o).symm

theorem caseCond_fails {ρ : Eval.Env} {x : Expr} (hx : Eval.eval p fuel ρ x = none) (sp : Span) :
    ∀ {es : List Expr} {c : Expr}, caseCond sp (some x) es = some c → Eval.eval p fuel ρ c = none
  | [], c, h => by simp [caseCond] at h
  | e :: es, c, h => by
    have ht : Eval.eval p fuel ρ (caseTest sp (some x) e) = none := by
      simp only [caseTest]; rw [Eval.eval]; simp [Eval.BinOp.ofString?, hx]
    simp only [caseCond] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact ht
    · simp only [Option.some.injEq] at h; subst h
      rw [Eval.eval]; simp [Eval.BinOp.ofString?, ht]

/-- When the switch expression has no value, neither has the chain, because
its first test evaluates the switch expression. -/
theorem chain_fails {ρ : Eval.Env} {x : Expr} (hx : Eval.eval p fuel ρ x = none) :
    ∀ (cs : List CaseClause) (dflt : Option (Span × List Stmt)) (d : Stmt), hasCase cs = true →
      switchChain (some x) dflt cs = some d → Eval.execStmt p fuel ρ d = none
  | [], _, _, h, _ => by simp [hasCase] at h
  | .mk sp none body :: rest, dflt, d, h, hd => by
    simp only [switchChain] at hd
    exact chain_fails hx rest _ d (by simpa [hasCase] using h) hd
  | .mk sp (some []) body :: rest, dflt, d, h, hd => by
    simp only [switchChain, caseCond] at hd
    exact chain_fails hx rest _ d (by simpa [hasCase] using h) hd
  | .mk sp (some (e :: es)) body :: rest, dflt, d, _, hd => by
    cases hc : caseCond sp (some x) (e :: es) with
    | none => exact absurd (caseCond_none hc) (by simp)
    | some c =>
      simp only [switchChain, hc, Option.some.injEq] at hd
      subst hd
      rw [execStmt_if_eq, caseCond_fails p fuel hx sp hc]
      rfl

theorem execStmt_switch_def (sp bsp : Span) (tag : Option Expr) (cs : List CaseClause)
    (ρ : Eval.Env) :
    Eval.execStmt p fuel ρ (.switchStmt sp none tag bsp cs) =
      (match tag with
        | none => some (Val.bool true)
        | some x => Eval.eval p fuel ρ x).bind fun v =>
          (Eval.execClauses p fuel ρ v cs none).map (leave ρ) := by
  rw [Eval.execStmt.eq_def]
  simp only [← bind_leave]
  cases tag <;> rfl

/-- An expression switch means what its chain of `if` statements means. -/
theorem execStmt_switch_chain {sp bsp : Span} {tag : Option Expr} {cs : List CaseClause} {d : Stmt}
    (hcase : tag.isSome = true → hasCase cs = true) (hd : switchChain tag none cs = some d)
    (ρ : Eval.Env) :
    Eval.execStmt p fuel ρ (.switchStmt sp none tag bsp cs) = Eval.execStmt p fuel ρ d := by
  rw [execStmt_switch_def]
  cases tag with
  | none =>
    have := chain_eval p fuel (ρ := ρ) (tag := none) (v := .bool true) rfl cs none
    simp only [hd, Option.map_none] at this
    simpa using this
  | some x =>
    cases hx : Eval.eval p fuel ρ x with
    | none =>
      simp only [hx, Option.bind_none]
      exact (chain_fails p fuel hx cs none d (hcase rfl) hd).symm
    | some v =>
      have := chain_eval p fuel (ρ := ρ) (tag := some x) (v := v) hx cs none
      simp only [hx, Option.bind_some]
      simp only [hd, Option.map_none] at this
      simpa using this

end tolean.Go.Proof
