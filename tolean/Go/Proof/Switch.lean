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
open tolean.Core (Res)

variable (p : Eval.Program) (fuel : Nat)

/-- The end of an implicit block: a return or a panic passes, and the names
that the block declared go out of scope. -/
def leave (ρ : Eval.Env) : Outcome → Outcome
  | .ret v => .ret v
  | .panic x => .panic x
  | .normal ρ' => .normal (ρ'.drop (ρ'.length - ρ.length))

theorem leave_leave (ρ : Eval.Env) (o : Outcome) : leave ρ (leave ρ o) = leave ρ o := by
  cases o with
  | ret v => rfl
  | panic x => rfl
  | normal ρ' =>
    simp only [leave, List.length_drop, Outcome.normal.injEq]
    have : ρ'.length - (ρ'.length - ρ.length) - ρ.length = 0 := by omega
    rw [this, List.drop_zero]

theorem leave_self (ρ : Eval.Env) : leave ρ (.normal ρ) = .normal ρ := by
  simp [leave]

theorem bind_leave (x : Option Outcome) (ρ : Eval.Env) :
    (x.bind fun
      | .ret v => some (.ret v)
      | .panic x => some (.panic x)
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
      | .panic x => some (.panic x)
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
    | panic x => simp [leave]
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
    | panic x => simp [leave]
    | normal ρ₁ =>
      simp only [Option.bind_some, exec_cons_eq, exec_nil_eq]
      cases h2 : Eval.execStmt p fuel ρ₁ (.switchStmt sp none tag bsp cs) with
      | none => simp [h2]
      | some o => cases o <;> simp [h2, leave]

/-! ### Case tests -/

/-- The boolean of a value, or a panic of the run that gave it. -/
def boolOf (r : Res Val Val) : Res Val Bool :=
  r.andThen fun
    | .bool b => Res.ok b
    | _ => none

/-- Run `k` on a boolean. A panic of the run that gave it is a panic of the
statement. -/
def withBool (r : Res Val Bool) (k : Bool → Option Outcome) : Option Outcome :=
  match r with
  | none => none
  | some (.error x) => some (.panic x)
  | some (.ok b) => k b

theorem withBool_map (r : Res Val Bool) (k : Bool → Option Outcome) (ρ : Eval.Env) :
    (withBool r k).map (leave ρ) = withBool r fun b => (k b).map (leave ρ) := by
  rcases r with _ | _ | b <;> rfl

/-- The switch expression `tag` has the value `v`, and a missing one is
`true`. -/
def TagVal (ρ : Eval.Env) : Option Expr → Val → Prop
  | none, v => v = .bool true
  | some x, v => Eval.eval p fuel ρ x = some (.ok v)

theorem caseTest_eval {ρ : Eval.Env} {tag : Option Expr} {v : Val} (ht : TagVal p fuel ρ tag v)
    (sp : Span) (e : Expr) :
    boolOf (Eval.eval p fuel ρ (caseTest sp tag e)) =
      (Eval.eval p fuel ρ e).andThen fun w => Res.lift (Eval.eqVal v w) := by
  cases tag with
  | none =>
    simp only [TagVal] at ht
    subst ht
    simp only [caseTest]
    rcases Eval.eval p fuel ρ e with _ | _ | w
    · rfl
    · rfl
    · cases w <;> simp [boolOf, Eval.eqVal, Res.lift]
  | some x =>
    simp only [TagVal] at ht
    simp only [caseTest]
    rw [Eval.eval]
    simp only [Eval.BinOp.ofString?, ht, Res.andThen_ok]
    rcases Eval.eval p fuel ρ e with _ | _ | w
    · rfl
    · rfl
    · simp only [Res.andThen_ok]
      cases v <;> cases w <;>
        simp [Eval.operate, Eval.binary, Eval.eqVal, boolOf, Res.lift]

theorem matchAny_nil (ρ : Eval.Env) (v : Val) : Eval.matchAny p fuel ρ v [] = some (.ok false) := by
  rw [Eval.matchAny]

theorem matchAny_cons (ρ : Eval.Env) (v : Val) (e : Expr) (es : List Expr) :
    Eval.matchAny p fuel ρ v (e :: es) =
      ((Eval.eval p fuel ρ e).andThen fun w => Res.lift (Eval.eqVal v w)).andThen fun b =>
        if b then Res.ok true else Eval.matchAny p fuel ρ v es := by
  rw [Eval.matchAny]
  rcases Eval.eval p fuel ρ e with _ | _ | w
  · rfl
  · rfl
  · simp only [Res.andThen_ok]
    cases Eval.eqVal v w with
    | none => rfl
    | some b => cases b <;> rfl

theorem or_bool (sp : Span) (l r : Expr) (ρ : Eval.Env) :
    boolOf (Eval.eval p fuel ρ (.binary sp "||" l r)) =
      (boolOf (Eval.eval p fuel ρ l)).andThen fun b =>
        if b then Res.ok true else boolOf (Eval.eval p fuel ρ r) := by
  rw [Eval.eval]
  simp only [Eval.BinOp.ofString?]
  rcases Eval.eval p fuel ρ l with _ | _ | lv
  · rfl
  · rfl
  · cases lv with
    | bool b =>
      cases b with
      | true => rfl
      | false =>
        simp only [Res.andThen_ok, boolOf, Bool.false_eq_true, ↓reduceIte]
        rcases Eval.eval p fuel ρ r with _ | _ | rv
        · rfl
        · rfl
        · cases rv <;> rfl
    | int _ => rfl
    | str _ => rfl

theorem caseCond_none {sp : Span} {tag : Option Expr} {es : List Expr} (h : caseCond sp tag es = none) :
    es = [] := by
  cases es with
  | nil => rfl
  | cons e es =>
    simp only [caseCond] at h
    split at h <;> simp at h

theorem caseCond_eval {ρ : Eval.Env} {tag : Option Expr} {v : Val} (ht : TagVal p fuel ρ tag v) (sp : Span) :
    ∀ {es : List Expr} {c : Expr}, caseCond sp tag es = some c →
      boolOf (Eval.eval p fuel ρ c) = Eval.matchAny p fuel ρ v es
  | [], c, h => by simp [caseCond] at h
  | e :: es, c, h => by
    rw [matchAny_cons]
    simp only [caseCond] at h
    split at h
    · next hn =>
      simp only [Option.some.injEq] at h
      subst h
      rw [caseCond_none hn, matchAny_nil, caseTest_eval p fuel ht sp e]
      rcases Eval.eval p fuel ρ e with _ | _ | w
      · rfl
      · rfl
      · simp only [Res.andThen_ok]
        cases Eval.eqVal v w with
        | none => rfl
        | some b => cases b <;> rfl
    · next r hr =>
      simp only [Option.some.injEq] at h
      subst h
      rw [or_bool, caseTest_eval p fuel ht sp e, caseCond_eval ht sp hr]

/-! ### The chain of `if` statements -/

theorem execStmt_if_eq (sp : Span) (c : Expr) (t : Stmt) (els : Option Stmt) (ρ : Eval.Env) :
    Eval.execStmt p fuel ρ (.ifStmt sp none c t els) =
      withBool (boolOf (Eval.eval p fuel ρ c)) fun b =>
        (if b then Eval.execStmt p fuel ρ t
          else match els with
            | some f => Eval.execStmt p fuel ρ f
            | none => some (.normal ρ)).map (leave ρ) := by
  rw [Eval.execStmt]
  rcases Eval.eval p fuel ρ c with _ | _ | w
  · rfl
  · rfl
  · cases w with
    | bool b =>
      simp only [Eval.withValue_ok, boolOf, Res.andThen_ok, withBool]
      rw [← bind_leave]
      cases b
      · cases els <;> rfl
      · rfl
    | int i => rfl
    | str s => rfl

theorem execClauses_case (sp : Span) (es : List Expr) (body : List Stmt) (rest : List CaseClause)
    (dflt : Option (List Stmt)) (ρ : Eval.Env) (v : Val) :
    Eval.execClauses p fuel ρ v (.mk sp (some es) body :: rest) dflt =
      withBool (Eval.matchAny p fuel ρ v es) fun b =>
        if b then Eval.exec p fuel ρ body else Eval.execClauses p fuel ρ v rest dflt := by
  rw [Eval.execClauses.eq_def]
  simp only
  rcases Eval.matchAny p fuel ρ v es with _ | _ | b
  · rfl
  · rfl
  · cases b <;> rfl

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
    simp only [switchChain]
    cases hc : caseCond sp tag es with
    | none =>
      rw [caseCond_none hc, execClauses_case, matchAny_nil]
      exact chain_eval ht rest dflt
    | some c =>
      simp only
      rw [execClauses_case, withBool_map, execStmt_if_eq, caseCond_eval p fuel ht sp hc]
      have ih := chain_eval ht rest dflt
      cases Eval.matchAny p fuel ρ v es with
      | none => rfl
      | some r =>
        rcases r with x | b
        · rfl
        · cases b with
          | true =>
            simp only [withBool, ↓reduceIte, block_eq, Option.map_map]
            congr 1; funext o; exact (leave_leave ρ o).symm
          | false =>
            simp only [withBool, Bool.false_eq_true, ↓reduceIte]
            cases hch : switchChain tag dflt rest with
            | none => simp only [hch] at ih; rw [ih]; simp [leave_self]
            | some f =>
              simp only [hch] at ih
              simp only
              rw [← ih, Option.map_map]
              congr 1; funext o; exact (leave_leave ρ o).symm

/-- A value that the switch expression does not have: it is stuck or it
panics. -/
def Stuck (r : Res Val Val) : Prop := ∀ v, r ≠ some (.ok v)

theorem stuck_andThen {r : Res Val Val} (hr : Stuck r) (f : Val → Res Val Val) :
    r.andThen f = r := by
  rcases r with _ | _ | v
  · rfl
  · rfl
  · exact absurd rfl (hr v)

theorem caseCond_fails {ρ : Eval.Env} {x : Expr} (hx : Stuck (Eval.eval p fuel ρ x)) (sp : Span) :
    ∀ {es : List Expr} {c : Expr}, caseCond sp (some x) es = some c →
      Eval.eval p fuel ρ c = Eval.eval p fuel ρ x
  | [], c, h => by simp [caseCond] at h
  | e :: es, c, h => by
    have ht : Eval.eval p fuel ρ (caseTest sp (some x) e) = Eval.eval p fuel ρ x := by
      simp only [caseTest]; rw [Eval.eval]; simp only [Eval.BinOp.ofString?]
      exact stuck_andThen hx _
    simp only [caseCond] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact ht
    · simp only [Option.some.injEq] at h; subst h
      rw [Eval.eval]; simp only [Eval.BinOp.ofString?, ht]
      exact stuck_andThen hx _

/-- When the switch expression has no value, the chain has the outcome of
the switch, because its first test evaluates the switch expression. -/
theorem chain_fails {ρ : Eval.Env} {x : Expr} (hx : Stuck (Eval.eval p fuel ρ x)) :
    ∀ (cs : List CaseClause) (dflt : Option (Span × List Stmt)) (d : Stmt), hasCase cs = true →
      switchChain (some x) dflt cs = some d →
        Eval.execStmt p fuel ρ d = Eval.withValue (Eval.eval p fuel ρ x) fun _ => none
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
      rcases hr : Eval.eval p fuel ρ x with _ | _ | v
      · rfl
      · rfl
      · exact absurd hr (hx v)

theorem execStmt_switch_def (sp bsp : Span) (tag : Option Expr) (cs : List CaseClause)
    (ρ : Eval.Env) :
    Eval.execStmt p fuel ρ (.switchStmt sp none tag bsp cs) =
      Eval.withValue (match tag with
        | none => Res.ok (Val.bool true)
        | some x => Eval.eval p fuel ρ x) fun v =>
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
    simp only
    rcases hx : Eval.eval p fuel ρ x with _ | _ | v
    · rw [chain_fails p fuel (by rw [hx]; simp [Stuck]) cs none d (hcase rfl) hd, hx]; rfl
    · rw [chain_fails p fuel (by rw [hx]; simp [Stuck]) cs none d (hcase rfl) hd, hx]; rfl
    · have := chain_eval p fuel (ρ := ρ) (tag := some x) (v := v) hx cs none
      simp only [Eval.withValue_ok]
      simp only [hd, Option.map_none] at this
      simpa using this

end tolean.Go.Proof
