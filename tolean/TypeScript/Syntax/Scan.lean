import tolean.TypeScript.Syntax.RoundTripExpr

/-!
Continuation-sensitive summaries of the type-argument probe. Unlike literal
token-skeleton equality, these summaries allow a field separator to be omitted
or changed inside braces. They preserve the actual probe in every surrounding
token context.
-/

namespace tolean.TypeScript.Syntax

/-- The probe's complete observation of a token fragment, including arbitrary
tokens before and after the fragment. Equality of these functions is a
congruence, not equality of the fragments themselves. -/
def scanView (tokens : List TokenKind) (before after : List TokenKind) : Bool :=
  closesKinds 0 (before ++ tokens ++ after)

def ScanEq (a b : List TokenKind) : Prop := scanView a = scanView b

theorem ScanEq.of_eq {a b : List TokenKind} (h : a = b) : ScanEq a b := by
  cases h
  rfl

theorem ScanEq.probeEquiv {a b : List TokenKind} (h : ScanEq a b) :
    ProbePrefixEquiv (closesKinds 0) a b := by
  intro before after
  exact congrFun (congrFun h before) after

theorem ScanEq.of_probeEquiv {a b : List TokenKind}
    (h : ProbePrefixEquiv (closesKinds 0) a b) : ScanEq a b := by
  funext before after
  exact h before after

theorem ScanEq.trans {a b c : List TokenKind} (h₁ : ScanEq a b) (h₂ : ScanEq b c) :
    ScanEq a c := Eq.trans h₁ h₂

theorem ScanEq.symm {a b : List TokenKind} (h : ScanEq a b) : ScanEq b a := Eq.symm h

theorem ScanEq.append {a b c d : List TokenKind} (h₁ : ScanEq a b) (h₂ : ScanEq c d) :
    ScanEq (a ++ c) (b ++ d) :=
  ScanEq.of_probeEquiv (h₁.probeEquiv.append h₂.probeEquiv)

/-- At depths at least `floor`, reading `tokens` either finds a `>` (`hit`),
or resumes the probe at the original depth. The continuation is arbitrary. -/
def ScanSummary (floor : Nat) (hit : Bool) (tokens : List TokenKind) : Prop :=
  ∀ depth, floor ≤ depth → ∀ after,
    closesKinds depth (tokens ++ after) = (hit || closesKinds depth after)

theorem ScanSummary.nil (floor : Nat) : ScanSummary floor false [] := by
  intro depth _ after
  rfl

theorem ScanSummary.weaken {low high : Nat} {hit : Bool} {tokens : List TokenKind}
    (h : ScanSummary low hit tokens) (hle : low ≤ high) :
    ScanSummary high hit tokens := by
  intro depth hd after
  exact h depth (Nat.le_trans hle hd) after

theorem ScanSummary.append {floor : Nat} {a b : List TokenKind} {ha hb : Bool}
    (h₁ : ScanSummary floor ha a) (h₂ : ScanSummary floor hb b) :
    ScanSummary floor (ha || hb) (a ++ b) := by
  intro depth hd after
  rw [List.append_assoc, h₁ depth hd, h₂ depth hd, Bool.or_assoc]

theorem ScanSummary.ident (name : String) : ScanSummary 0 false [.ident name] := by
  intro depth _ after
  rfl

theorem ScanSummary.keyword (name : String) : ScanSummary 0 false [.keyword name] := by
  intro depth _ after
  rfl

theorem ScanSummary.comma : ScanSummary 0 false [.punct ","] := by
  intro depth _ after
  rfl

theorem ScanSummary.colon : ScanSummary 0 false [.punct ":"] := by
  intro depth _ after
  rfl

theorem ScanSummary.question : ScanSummary 0 false [.punct "?"] := by
  intro depth _ after
  rfl

/-- A semicolon is neutral only at positive depth; it must not be dropped
unconditionally from the skeleton. -/
theorem ScanSummary.semicolon : ScanSummary 1 false [.punct ";"] := by
  intro depth hd after
  have hne : depth ≠ 0 := by omega
  simp [closesKinds, hne]

theorem ScanSummary.greater : ScanSummary 0 true [.punct ">"] := by
  intro depth _ after
  rfl

/-- Enclosing a positive-depth summary makes it valid even at depth zero. -/
theorem ScanSummary.enclose {hit : Bool} {tokens : List TokenKind}
    (h : ScanSummary 1 hit tokens) {opening closing : String}
    (ho : opening = "(" ∨ opening = "[" ∨ opening = "{")
    (hc : closing = ")" ∨ closing = "]" ∨ closing = "}") :
    ScanSummary 0 hit (.punct opening :: tokens ++ [.punct closing]) := by
  intro depth _ after
  have hs := h (depth + 1) (by omega) (.punct closing :: after)
  rcases ho with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
  all_goals
    simpa [List.append_assoc, closesKinds] using hs

/-- Equality of the probe on a prefix at every depth and continuation remains
equality when any source tokens precede that prefix. -/
theorem probePrefixEquiv_of_continuations {a b : List TokenKind}
    (h : ∀ depth after, closesKinds depth (a ++ after) = closesKinds depth (b ++ after)) :
    ProbePrefixEquiv (closesKinds 0) a b := by
  intro before after
  have hbefore : ∀ depth,
      closesKinds depth (before ++ a ++ after) =
        closesKinds depth (before ++ b ++ after) := by
    induction before with
    | nil => intro depth; exact h depth after
    | cons token before ih =>
      intro depth
      cases token with
      | punct p =>
        simp only [List.cons_append, closesKinds]
        split <;> simp_all
      | eof => rfl
      | _ => exact ih depth
  exact hbefore 0

/-- Summaries with the same hit flag may replace one another in every probe
context. This is the congruence needed by expression composition. -/
theorem ScanSummary.probeEquiv {hit : Bool} {a b : List TokenKind}
    (ha : ScanSummary 0 hit a) (hb : ScanSummary 0 hit b) :
    ProbePrefixEquiv (closesKinds 0) a b := by
  apply probePrefixEquiv_of_continuations
  intro depth after
  exact (ha depth (Nat.zero_le _) after).trans (hb depth (Nat.zero_le _) after).symm

theorem ScanSummary.scanEq {hit : Bool} {a b : List TokenKind}
    (ha : ScanSummary 0 hit a) (hb : ScanSummary 0 hit b) : ScanEq a b :=
  ScanEq.of_probeEquiv (ha.probeEquiv hb)

/-- In particular, insertion of field semicolons inside braces preserves the
probe without asserting false literal equality of source and printed tokens. -/
theorem probePrefixEquiv_emptyObjectSeparator :
    ProbePrefixEquiv (closesKinds 0)
      [.punct "{", .punct "}"] [.punct "{", .punct ";", .punct "}"] := by
  exact (ScanSummary.enclose (ScanSummary.nil 1) (.inr (.inr rfl)) (.inr (.inr rfl))).probeEquiv
    (ScanSummary.enclose ScanSummary.semicolon (.inr (.inr rfl)) (.inr (.inr rfl)))

end tolean.TypeScript.Syntax
