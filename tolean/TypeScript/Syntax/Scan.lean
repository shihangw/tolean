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

@[simp] theorem ScanEq.refl (tokens : List TokenKind) : ScanEq tokens tokens := rfl

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

theorem ScanEq.cons {a b : List TokenKind} {token : TokenKind} (h : ScanEq a b) :
    ScanEq (token :: a) (token :: b) :=
  (show ScanEq [token] [token] from rfl).append h

theorem closesKinds_openPrefix (count depth : Nat) (after : List TokenKind) :
    closesKinds depth (List.replicate count (.punct "{") ++ after) =
      closesKinds (depth + count) after := by
  induction count generalizing depth with
  | zero => simp
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, closesKinds]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (depth + 1)

theorem ScanEq.at_depth {a b : List TokenKind} (h : ScanEq a b) (depth : Nat)
    (after : List TokenKind) :
    closesKinds depth (a ++ after) = closesKinds depth (b ++ after) := by
  have hp := h.probeEquiv (List.replicate depth (.punct "{")) after
  simpa only [List.append_assoc, closesKinds_openPrefix, Nat.zero_add] using hp

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

theorem ScanSummary.of_scanEq {floor : Nat} {hit : Bool} {a b : List TokenKind}
    (h : ScanSummary floor hit b) (heq : ScanEq a b) : ScanSummary floor hit a := by
  intro depth hd after
  exact (heq.at_depth depth after).trans (h depth hd after)

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

theorem ScanSummary.bar : ScanSummary 0 false [.punct "|"] := by
  intro depth _ after
  rfl

theorem ScanSummary.less : ScanSummary 0 false [.punct "<"] := by
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

/-- A fragment with some stable probe summary. -/
def ScanSafe (floor : Nat) (tokens : List TokenKind) : Prop :=
  ∃ hit, ScanSummary floor hit tokens

theorem ScanSafe.append {floor : Nat} {a b : List TokenKind}
    (ha : ScanSafe floor a) (hb : ScanSafe floor b) : ScanSafe floor (a ++ b) := by
  obtain ⟨aHit, ha⟩ := ha
  obtain ⟨bHit, hb⟩ := hb
  exact ⟨aHit || bHit, ha.append hb⟩

theorem ScanSafe.weaken {low high : Nat} {tokens : List TokenKind}
    (h : ScanSafe low tokens) (hle : low ≤ high) : ScanSafe high tokens := by
  obtain ⟨hit, h⟩ := h
  exact ⟨hit, h.weaken hle⟩

theorem ScanSafe.enclose {tokens : List TokenKind} (h : ScanSafe 1 tokens)
    {opening closing : String} (ho : opening = "(" ∨ opening = "[" ∨ opening = "{")
    (hc : closing = ")" ∨ closing = "]" ∨ closing = "}") :
    ScanSafe 0 (.punct opening :: tokens ++ [.punct closing]) := by
  obtain ⟨hit, h⟩ := h
  exact ⟨hit, h.enclose ho hc⟩

theorem ScanSafe.joined {separator : String}
    (hsep : ScanSummary 0 false [.punct separator]) :
    ∀ (items : List (List TokenKind)),
      (∀ item ∈ items, ScanSafe 0 item) → ScanSafe 0 (joined separator items)
  | [], _ => ⟨false, ScanSummary.nil 0⟩
  | [item], h => by simpa [joined] using h item (by simp)
  | item :: next :: items, h => by
    have htail := ScanSafe.joined hsep (next :: items) (fun x hx => h x (by simp [hx]))
    simpa only [joined, List.singleton_append] using
      (h item (by simp)).append ((show ScanSafe 0 [.punct separator] from ⟨false, hsep⟩).append htail)

theorem ScanSafe.propertyName_safe (name : String) : ScanSafe 0 (propertyName name) := by
  unfold propertyName
  split
  · exact ⟨false, ScanSummary.keyword name⟩
  · exact ⟨false, ScanSummary.ident name⟩

theorem ScanSummary.propertyName_safe (name : String) :
    ScanSummary 0 false (propertyName name) := by
  unfold propertyName
  split
  · exact ScanSummary.keyword name
  · exact ScanSummary.ident name

theorem ScanSummary.field {hit : Bool} {type : TypeExpr}
    (htype : ScanSummary 0 hit type.tokens) (sp : Span) (readonly : Bool)
    (name : String) (optional : Bool) :
    ScanSummary 1 hit (TypeField.field sp readonly name optional type).tokens := by
  rw [TypeField.tokens_field]
  have hreadonly : ScanSummary 1 false (if readonly then [.ident "readonly"] else []) := by
    cases readonly
    · exact ScanSummary.nil 1
    · exact (ScanSummary.ident "readonly").weaken (by decide)
  have hoptional : ScanSummary 1 false (if optional then [.punct "?"] else []) := by
    cases optional
    · exact ScanSummary.nil 1
    · exact ScanSummary.question.weaken (by decide)
  simpa only [Bool.false_or, Bool.or_false] using
    ((((hreadonly.append ((ScanSummary.propertyName_safe name).weaken (by decide))).append hoptional).append
      (ScanSummary.colon.weaken (by decide))).append (htype.weaken (by decide))).append ScanSummary.semicolon

mutual

theorem TypeExpr.scanSafe : ∀ type : TypeExpr, ScanSafe 0 type.tokens
  | .predicate _ name type => by
    simpa only [TypeExpr.tokens, TypeExpr.words, identWord, List.flatten_cons,
      List.singleton_append] using
      (show ScanSafe 0 [.ident name] from ⟨false, ScanSummary.ident name⟩).append
        ((show ScanSafe 0 [.ident "is"] from ⟨false, ScanSummary.ident "is"⟩).append type.scanSafe)
  | .keyword _ name => by
    simp only [TypeExpr.tokens, TypeExpr.words]
    split <;> first
      | exact ⟨false, ScanSummary.keyword name⟩
      | exact ⟨false, ScanSummary.ident name⟩
  | .null _ => ⟨false, ScanSummary.keyword "null"⟩
  | .literal _ lit => by
    cases lit with
    | string value | number value | bigint value =>
      exact ⟨false, by intro depth _ after; rfl⟩
    | bool value =>
      exact ⟨false, ScanSummary.keyword (if value then "true" else "false")⟩
  | .ref sp name args => by
    cases args with
    | nil => exact ⟨false, ScanSummary.ident name⟩
    | cons arg args =>
      rw [tokens_ref sp name (arg :: args) (by simp)]
      have hargs := TypeExpr.scanSafe_joined "," ScanSummary.comma (arg :: args)
      simpa only [List.singleton_append] using
        (show ScanSafe 0 [.ident name] from ⟨false, ScanSummary.ident name⟩).append
          ((show ScanSafe 0 [.punct "<"] from ⟨false, ScanSummary.less⟩).append
            (hargs.append ⟨true, ScanSummary.greater⟩))
  | .array sp type => by
    rw [TypeExpr.tokens_array]
    exact type.scanSafe.append
      ((show ScanSafe 1 [] from ⟨false, ScanSummary.nil 1⟩).enclose (.inr (.inl rfl)) (.inr (.inl rfl)))
  | .paren sp type => by
    rw [TypeExpr.tokens_paren]
    exact (type.scanSafe.weaken (by decide)).enclose (.inl rfl) (.inl rfl)
  | .tuple sp readonly types => by
    have hs : ScanSafe 0 (TypeExpr.tuple sp false types).tokens := by
      rw [tokens_tuple]
      exact ((TypeExpr.scanSafe_joined "," ScanSummary.comma types).weaken (by decide)).enclose
        (.inr (.inl rfl)) (.inr (.inl rfl))
    cases readonly with
    | false => exact hs
    | true =>
      rw [tokens_readonly]
      exact (show ScanSafe 0 [.ident "readonly"] from ⟨false, ScanSummary.ident "readonly"⟩).append hs
  | .union sp types => by
    cases types with
    | nil => exact ⟨false, ScanSummary.nil 0⟩
    | cons type types =>
      cases types with
      | nil =>
        rw [tokens_union_one]
        exact (show ScanSafe 0 [.punct "|"] from ⟨false, ScanSummary.bar⟩).append type.scanSafe
      | cons next types =>
        simpa only [TypeExpr.tokens, TypeExpr.words, separated_flatten, wordsOf_eq,
          List.map_map, Function.comp_def] using
          TypeExpr.scanSafe_joined "|" ScanSummary.bar (type :: next :: types)
  | .object sp fields => by
    rw [tokens_object]
    exact (TypeField.scanSafe_all fields).enclose (.inr (.inr rfl)) (.inr (.inr rfl))

theorem TypeExpr.scanSafe_joined (separator : String)
    (hsep : ScanSummary 0 false [.punct separator]) (types : List TypeExpr) :
    ScanSafe 0 (joined separator (types.map TypeExpr.tokens)) := by
  apply ScanSafe.joined hsep
  intro tokens htokens
  obtain ⟨type, _, rfl⟩ := List.mem_map.mp htokens
  exact type.scanSafe

theorem TypeField.scanSafe : ∀ field : TypeField, ScanSafe 1 field.tokens
  | .field sp readonly name optional type => by
    rw [TypeField.tokens_field]
    have hreadonly : ScanSafe 1 (if readonly then [.ident "readonly"] else []) := by
      cases readonly
      · exact ⟨false, ScanSummary.nil 1⟩
      · exact ⟨false, (ScanSummary.ident "readonly").weaken (by decide)⟩
    have hoptional : ScanSafe 1 (if optional then [.punct "?"] else []) := by
      cases optional
      · exact ⟨false, ScanSummary.nil 1⟩
      · exact ⟨false, ScanSummary.question.weaken (by decide)⟩
    exact ((((hreadonly.append ((ScanSafe.propertyName_safe name).weaken (by decide))).append hoptional).append
      ⟨false, ScanSummary.colon.weaken (by decide)⟩).append (type.scanSafe.weaken (by decide))).append
        ⟨false, ScanSummary.semicolon⟩

theorem TypeField.scanSafe_all : ∀ fields : List TypeField, ScanSafe 1 (TypeField.tokensOf fields)
  | [] => ⟨false, ScanSummary.nil 1⟩
  | field :: fields => field.scanSafe.append (TypeField.scanSafe_all fields)

end

end tolean.TypeScript.Syntax
