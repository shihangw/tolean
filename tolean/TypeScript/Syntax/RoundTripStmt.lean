import tolean.TypeScript.Syntax.RoundTripExpr

/-!
The parser's round trip for statements, on tokens: the parser reads the
tokens that `Syntax/Source.lean` prints for a statement as the same
statement, apart from spans.

The printer writes a statement as lines of words. `Laid ts lines` states that
the tokens `ts` are those lines: the tokens of a word touch, a line break
comes before the first token of each line after the first, and none comes
before another token. `Stmt.wf T fn loop st` is the condition under which
the proofs here show that `parseStatement` reads `st`: the target edition is
`T`, and the statement is in a function if `fn` holds and in a loop if `loop`
holds. An `if` with an `else` needs a branch that does not
end with an `if` without `else`, since that `if` would take the `else`.
-/
namespace tolean.TypeScript.Syntax

open tolean

set_option linter.unusedSimpArgs false

/-! ### Lines of tokens -/

/-- `ts` are the tokens of the lines of words `ls`, one line after another.
The tokens of each line touch as `Touching` states. A line break comes before
the first token of each line after the first, and none comes before any other
token of a line. -/
def Laid : List Token → List (List Word) → Prop
  | ts, [] => ts = []
  | ts, l :: ls => ∃ a b, ts = a ++ b ∧ Touching a l ∧ (∀ y ∈ a.tail, y.newlineBefore = false) ∧
      (∀ y ∈ b.head?, y.newlineBefore = true) ∧ Laid b ls

/-- The words of each line of a statement. They do not depend on how far in
the statement is. -/
def Stmt.wordLines (st : Stmt) : List (List Word) := (st.lines 0).map Prod.snd

mutual

theorem Stmt.lines_words : ∀ (st : Stmt) (d : Nat), (st.lines d).map Prod.snd = (st.lines 0).map Prod.snd
  | .ifStmt _ test t none, d => by simp [Stmt.lines, Stmt.lines_words t (d + 1), Stmt.lines_words t 1]
  | .ifStmt _ test t (some e), d => by
    simp [Stmt.lines, Stmt.lines_words t (d + 1), Stmt.lines_words t 1, Stmt.lines_words e (d + 1),
      Stmt.lines_words e 1]
  | .forOfStmt _ _ _ _ body, d => by simp [Stmt.lines, Stmt.lines_words body (d + 1), Stmt.lines_words body 1]
  | .whileStmt _ _ body, d => by simp [Stmt.lines, Stmt.lines_words body (d + 1), Stmt.lines_words body 1]
  | .block _ body, d => by simp [Stmt.lines, Stmt.linesOf_words body (d + 1), Stmt.linesOf_words body 1]
  | .varDecl .., _ | .exprStmt .., _ | .returnStmt _ none, _ | .returnStmt _ (some _), _ | .breakStmt _, _
  | .continueStmt _, _ | .empty _, _ => by simp [Stmt.lines]

theorem Stmt.linesOf_words : ∀ (ss : List Stmt) (d : Nat),
    (Stmt.linesOf d ss).map Prod.snd = (Stmt.linesOf 0 ss).map Prod.snd
  | [], _ => rfl
  | s :: ss, d => by simp [Stmt.linesOf, Stmt.lines_words s d, Stmt.linesOf_words ss d]

end

theorem Laid.append : ∀ {ts : List Token} {l₁ l₂ : List (List Word)}, Laid ts (l₁ ++ l₂) →
    ∃ a b, ts = a ++ b ∧ Laid a l₁ ∧ Laid b l₂ ∧ (l₁ ≠ [] → ∀ y ∈ b.head?, y.newlineBefore = true)
  | ts, [], l₂, h => ⟨[], ts, rfl, rfl, h, fun h => absurd rfl h⟩
  | ts, l :: l₁, l₂, h => by
    obtain ⟨a, b, rfl, ha, hn, hb, h'⟩ := h
    obtain ⟨b₁, b₂, rfl, h₁, h₂, h₃⟩ := Laid.append h'
    refine ⟨a ++ b₁, b₂, by simp, ⟨a, b₁, rfl, ha, hn, ?_, h₁⟩, h₂, fun _ => ?_⟩
    · intro y hy
      exact hb y (by cases b₁ <;> simp_all)
    · cases l₁ with
      | nil =>
        simp [Laid] at h₁; subst h₁; simpa using hb
      | cons _ _ => exact h₃ (by simp)

/-- One line, which a line break or nothing follows. -/
theorem Laid.one {ts : List Token} {l : List Word} (h : Laid ts [l]) :
    Touching ts l ∧ ∀ y ∈ ts.tail, y.newlineBefore = false := by
  obtain ⟨a, b, rfl, ha, hn, _, hb⟩ := h
  simp [Laid] at hb; subst hb; simpa using ⟨ha, hn⟩

/-- A line, and the lines after it. -/
theorem Laid.cons {ts : List Token} {l : List Word} {ls : List (List Word)} (h : Laid ts (l :: ls)) :
    ∃ a b, ts = a ++ b ∧ Touching a l ∧ (∀ y ∈ a.tail, y.newlineBefore = false) ∧
      (∀ y ∈ b.head?, y.newlineBefore = true) ∧ Laid b ls := h


/-! ### Well-formed statements -/

/-- A first token that `parseStatement` hands to `parseExpressionStatement`:
not a `{`, which starts a block, not `let`, which starts a declaration, and no
keyword but those that start an expression. -/
def startsExprStmt : Option TokenKind → Bool
  | some (.punct "{") | some (.ident "let") => false
  | some (.keyword w) => w == "true" || w == "false" || w == "null" || w == "typeof" || w == "void"
  | _ => true

/-- A statement that ends with an `if` without `else`. An `else` after it would
join that `if`. -/
def Stmt.openIf : Stmt → Bool
  | .ifStmt _ _ _ none => true
  | .ifStmt _ _ _ (some e) => e.openIf
  | .whileStmt _ _ b | .forOfStmt _ _ _ _ b => b.openIf
  | _ => false

/-- A declaration, which JavaScript does not allow as the body of `if`, `for`
or `while`. -/
def Stmt.isDecl : Stmt → Bool
  | .varDecl .. => true
  | _ => false

def VarDecl.wf (T : Edition) (d : VarDecl) : Bool :=
  exprName d.name && (match d.type with | some t => t.wf | none => true) &&
    (match d.init with | some e => e.wfAt T .assign && e.afterOK [.punct ";"] | none => d.kind == .«let»)

/-- An expression in `( … )` after `if`, `while` or `for … of`. -/
def Expr.wfParen (T : Edition) (e : Expr) : Bool := e.wfAt T .assign && e.afterOK [.punct ")"]

mutual

/-- `st` is a statement that `parseStatement` reads when the target edition is
`T`, in a function if `fn` holds and in a loop if `loop` holds. -/
def Stmt.wf (T : Edition) (fn loop : Bool) : Stmt → Bool
  | .varDecl _ d => d.wf T
  | .exprStmt _ e => e.wfAt T .assign && e.afterOK [.punct ";"] && startsExprStmt e.tokens.head?
  | .returnStmt _ none => fn
  | .returnStmt _ (some e) => fn && e.wfAt T .assign && e.afterOK [.punct ";"]
  | .ifStmt _ test t none => test.wfParen T && !t.isDecl && t.wf T fn loop
  | .ifStmt _ test t (some e) =>
    test.wfParen T && !t.isDecl && t.wf T fn loop && !t.openIf && !e.isDecl && e.wf T fn loop
  | .forOfStmt _ _ name it body => exprName name && it.wfParen T && !body.isDecl && body.wf T fn true
  | .whileStmt _ test body => test.wfParen T && !body.isDecl && body.wf T fn true
  | .block _ body => Stmt.allWF T fn loop body
  | .breakStmt _ | .continueStmt _ => loop
  | .empty _ => true

def Stmt.allWF (T : Edition) (fn loop : Bool) : List Stmt → Bool
  | [] => true
  | s :: ss => s.wf T fn loop && Stmt.allWF T fn loop ss

end

mutual

/-- How deep the statements of `st` nest. -/
def Stmt.depth : Stmt → Nat
  | .ifStmt _ _ t none => t.depth + 1
  | .ifStmt _ _ t (some e) => max t.depth e.depth + 1
  | .forOfStmt _ _ _ _ b | .whileStmt _ _ b => b.depth + 1
  | .block _ body => Stmt.depthOf body + 1
  | .varDecl .. | .exprStmt .. | .returnStmt .. | .breakStmt _ | .continueStmt _ | .empty _ => 0

def Stmt.depthOf : List Stmt → Nat
  | [] => 0
  | s :: ss => max s.depth (Stmt.depthOf ss)

end

/-! ### Fuel for a type -/

theorem TypeExpr.tokens_paren (sp : Span) (i : TypeExpr) :
    (TypeExpr.paren sp i).tokens = .punct "(" :: i.tokens ++ [.punct ")"] := by
  simp [TypeExpr.tokens, TypeExpr.words, punctWord]

theorem TypeExpr.tokens_array (sp : Span) (e : TypeExpr) :
    (TypeExpr.array sp e).tokens = e.tokens ++ [.punct "[", .punct "]"] := by
  simp [TypeExpr.tokens, TypeExpr.words, punctWord]

mutual

/-- A type nests no deeper than it has tokens. -/
theorem TypeExpr.height_le : ∀ t : TypeExpr, t.height ≤ t.tokens.length
  | .ref _ _ [] => by simp [TypeExpr.height, TypeExpr.heightOf, TypeExpr.tokens, TypeExpr.words, identWord]
  | .ref sp n (a :: as) => by
    have := TypeExpr.heightOf_le (a :: as)
    rw [tokens_ref sp n _ (by simp)]
    simp only [TypeExpr.height, List.length_cons, List.length_append, List.length_nil]; omega
  | .paren sp i => by
    have := TypeExpr.height_le i
    rw [TypeExpr.tokens_paren]; simp only [TypeExpr.height, List.length_cons, List.length_append, List.length_nil]
    omega
  | .array sp e => by
    have := TypeExpr.height_le e
    rw [TypeExpr.tokens_array]; simp only [TypeExpr.height, List.length_cons, List.length_append, List.length_nil]
    omega
  | .union _ [] => by simp [TypeExpr.height, TypeExpr.heightOf]
  | .union sp [m] => by
    have := TypeExpr.height_le m
    rw [tokens_union_one]; simp only [TypeExpr.height, TypeExpr.heightOf, List.length_cons]; omega
  | .union sp (m₁ :: m₂ :: ms) => by
    have := TypeExpr.height_le m₁; have := TypeExpr.heightOf_le_bars (m₂ :: ms)
    rw [tokens_union]
    simp only [TypeExpr.height, TypeExpr.heightOf, List.length_append] at this ⊢; omega
  | .keyword .. | .null _ | .literal .. => by simp [TypeExpr.height]

theorem TypeExpr.heightOf_le : ∀ ts : List TypeExpr, TypeExpr.heightOf ts ≤ (joined "," (ts.map TypeExpr.tokens)).length
  | [] => by simp [TypeExpr.heightOf, joined]
  | [t] => by have := TypeExpr.height_le t; simp [TypeExpr.heightOf, joined]; omega
  | t :: u :: ts => by
    have := TypeExpr.height_le t; have := TypeExpr.heightOf_le (u :: ts)
    show max t.height (TypeExpr.heightOf (u :: ts)) ≤
      (t.tokens ++ .punct "," :: joined "," ((u :: ts).map TypeExpr.tokens)).length
    simp only [List.length_append, List.length_cons]; omega

theorem TypeExpr.heightOf_le_bars : ∀ ts : List TypeExpr,
    TypeExpr.heightOf ts ≤ (ts.map fun i => .punct "|" :: i.tokens).flatten.length
  | [] => by simp [TypeExpr.heightOf]
  | t :: ts => by
    have := TypeExpr.height_le t; have := TypeExpr.heightOf_le_bars ts
    simp only [TypeExpr.heightOf, List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

end

/-- `parseType`, with the fuel that `budget` gives, reads every type. -/
theorem parseType_budget (t : TypeExpr) (ht : t.wf = true) :
    ∀ (s : ParseState) (ts rest : List Token), s.rest = ts ++ rest → s.left = s.rest.length →
      ts.map (·.kind) = t.tokens → (∀ y ∈ ts, y.newlineBefore = false) → rest ≠ [] → FollowsType rest →
      ∃ t' s', Parse.parseType (10 * (s.left + 1)) s = .ok t' s' ∧ t'.erase = t.erase ∧ Leaves s s' rest := by
  intro s ts rest hs hl hk hn hr hf
  have h1 := TypeExpr.height_le t
  have h2 : ts.length = t.tokens.length := by rw [← hk, List.length_map]
  have h3 : ts.length ≤ s.left := by rw [hl, hs, List.length_append]; omega
  exact (types_reads _).1 t ht (by omega) s ts rest hs hl hk hn hr hf


/-! ### Declarations of variables -/

theorem readName_ok {s : ParseState} {x u : Token} {r : List Token} {name : String}
    (hs : s.rest = x :: u :: r) (hx : x.kind = .ident name) (hn : name ∉ Parse.refusedNames) :
    Parse.readName s = .ok name (advanced s x u r) := by
  simp [Parse.readName, Parse.advance_eq hs, hx, hn, bind, EStateM.bind, pure, EStateM.pure]

theorem endStatement_semi {s : ParseState} {x : Token} {r : List Token} (hs : s.rest = x :: r) (hr : r ≠ [])
    (hx : x.kind = .punct ";") :
    Parse.endStatement s = .ok () { s with rest := r, left := s.left - 1, lastStop := x.span.stop } := by
  simp only [Parse.endStatement]
  rw [Parse.bind_eq (Parse.peek_eq hs)]
  simp only [Token.isPunct, hx, beq_self_eq_true, ↓reduceIte]
  exact Parse.discard_eq (Parse.advance_cons hs hr)

/-- The token of `const` or `let`. -/
def VarKind.token : VarKind → TokenKind
  | .const => .keyword "const"
  | .«let» => .ident "let"

theorem VarKind.word_eq (k : VarKind) : k.word = [k.token] := by cases k <;> rfl

/-- A type in a declaration ends before `=` or `;`. -/
theorem followsType_eq_semi {u : Token} {r : List Token} (hu : u.kind = .punct "=" ∨ u.kind = .punct ";") :
    FollowsType (u :: r) := by
  rcases hu with hu | hu <;> exact followsType_punct hu (by simp)

/-- `const x: T = e;` or `let x: T = e;`. -/
theorem varDecl_ss {T : Edition} (kind : VarKind) (name : String) (t : TypeExpr) (e : Expr)
    (hd : VarDecl.wf T ⟨kind, name, some t, some e⟩ = true)
    (s : ParseState) (ts rest : List Token) (hT : s.target = T) (hs : s.rest = ts ++ rest)
    (hl : s.left = s.rest.length) (ht : Touching ts (VarDecl.words ⟨kind, name, some t, some e⟩))
    (hn : ∀ y ∈ ts.tail, y.newlineBefore = false) (hr : rest ≠ []) :
    ∃ d' s', Parse.parseVarDecl s = .ok d' s' ∧ d'.erase = VarDecl.erase ⟨kind, name, some t, some e⟩ ∧
      Leaves s s' rest := by
  simp only [VarDecl.wf, Bool.and_eq_true] at hd
  obtain ⟨⟨hname, hwt⟩, hwe, hae⟩ := hd
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  simp only [VarDecl.words, VarKind.word_eq] at ht
  obtain ⟨kw, ts₁, rfl, hkw, h₁⟩ := Touching.cons_one (by simpa using ht)
  obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  obtain ⟨colon, ts₃, rfl, hcolon, h₃⟩ := Touching.cons_one (by simpa [punctWord] using h₂)
  obtain ⟨tts, ts₄, rfl, htt, h₄⟩ := Touching.append_split h₃
  obtain ⟨eq, ts₅, rfl, heq, h₅⟩ := Touching.cons_one (by simpa [punctWord] using h₄)
  obtain ⟨ets, ts₆, rfl, het, h₆⟩ := Touching.append_split h₅
  obtain ⟨semi, ts₇, rfl, hsemi, h₇⟩ := Touching.cons_one (by simpa [punctWord] using h₆)
  simp [Touching] at h₇; subst h₇
  have hs' : s.rest = kw :: nm :: colon :: (tts ++ eq :: (ets ++ semi :: rest)) := by simpa using hs
  let s₁ := advanced s kw nm (colon :: (tts ++ eq :: (ets ++ semi :: rest)))
  let s₂ := advanced s₁ nm colon (tts ++ eq :: (ets ++ semi :: rest))
  let s₃ : ParseState := { s₂ with rest := tts ++ eq :: (ets ++ semi :: rest), left := s₂.left - 1, lastStop := colon.span.stop }
  have hl₃ : s₃.left = s₃.rest.length := by simp [s₃, s₂, s₁, hl, hs']
  obtain ⟨t', s₄, hpt, het', hL₄⟩ := parseType_budget t hwt s₃ tts (eq :: (ets ++ semi :: rest)) rfl hl₃
    htt.kinds (fun y hy => hn y (by simp [hy])) (by simp) (followsType_eq_semi (.inl heq))
  have hs₄ : s₄.rest = eq :: (ets ++ semi :: rest) := hL₄.rest_eq
  have hl₄ : s₄.left = s₄.rest.length := by rw [hL₄.left_eq, hL₄.rest_eq]
  let s₅ : ParseState := { s₄ with rest := ets ++ semi :: rest, left := s₄.left - 1, lastStop := eq.span.stop }
  have hl₅ : s₅.left = s₅.rest.length := by simp [s₅, hl₄, hs₄]
  have hT₅ : s₅.target = T := by simp [s₅, hL₄.target_eq, s₃, s₂, s₁, hT]
  obtain ⟨e', s₆, hpe, he', hL₆⟩ := parseAssign_budget e hwe s₅ ets (semi :: rest) hT₅ rfl hl₅ het
    (fun y hy => hn y (by simp [List.mem_of_mem_tail hy])) (by simp)
    (endsAssign_separator hsemi (by simp [separators])) (by simpa [hsemi] using afterOK_semicolon hae _)
  have hs₆ : s₆.rest = semi :: rest := hL₆.rest_eq
  have hnot : nm.kind ≠ .punct "[" ∧ nm.kind ≠ .punct "{" := by rw [hnm]; simp
  refine ⟨⟨kind, name, some t', some e'⟩, { s₆ with rest := rest, left := s₆.left - 1, lastStop := semi.span.stop },
    ?_, by simp [VarDecl.erase, het', he'], ?_⟩
  · simp only [Parse.parseVarDecl]
    rw [Parse.bind_eq (Parse.advance_eq hs'), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hnot] at h)]
    rw [Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname'), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, hcolon]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₂) rfl (by simp))),
      Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpt, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₄)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, heq]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs₄ (by simp))),
      Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpe, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₆)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, hsemi]
    rw [Parse.bind_eq (endStatement_semi hs₆ hr hsemi)]
    cases kind <;> simp [hkw, VarKind.token, pure, EStateM.pure]
  · exact leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])) (leaves_trans hL₄
        (leaves_trans (leaves_advance hs₄ hl₄) (leaves_trans hL₆ (leaves_advance hs₆ (by rw [hL₆.left_eq, hs₆])))))))

/-- `const x = e;` or `let x = e;`. -/
theorem varDecl_ns {T : Edition} (kind : VarKind) (name : String) (e : Expr)
    (hd : VarDecl.wf T ⟨kind, name, none, some e⟩ = true)
    (s : ParseState) (ts rest : List Token) (hT : s.target = T) (hs : s.rest = ts ++ rest)
    (hl : s.left = s.rest.length) (ht : Touching ts (VarDecl.words ⟨kind, name, none, some e⟩))
    (hn : ∀ y ∈ ts.tail, y.newlineBefore = false) (hr : rest ≠ []) :
    ∃ d' s', Parse.parseVarDecl s = .ok d' s' ∧ d'.erase = VarDecl.erase ⟨kind, name, none, some e⟩ ∧
      Leaves s s' rest := by
  simp only [VarDecl.wf, Bool.and_eq_true] at hd
  obtain ⟨⟨hname, -⟩, hwe, hae⟩ := hd
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  simp only [VarDecl.words, VarKind.word_eq] at ht
  obtain ⟨kw, ts₁, rfl, hkw, h₁⟩ := Touching.cons_one (by simpa using ht)
  obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  obtain ⟨eq, ts₅, rfl, heq, h₅⟩ := Touching.cons_one (by simpa [punctWord] using h₂)
  obtain ⟨ets, ts₆, rfl, het, h₆⟩ := Touching.append_split h₅
  obtain ⟨semi, ts₇, rfl, hsemi, h₇⟩ := Touching.cons_one (by simpa [punctWord] using h₆)
  simp [Touching] at h₇; subst h₇
  have hs' : s.rest = kw :: nm :: eq :: (ets ++ semi :: rest) := by simpa using hs
  let s₁ := advanced s kw nm (eq :: (ets ++ semi :: rest))
  let s₂ := advanced s₁ nm eq (ets ++ semi :: rest)
  let s₅ : ParseState := { s₂ with rest := ets ++ semi :: rest, left := s₂.left - 1, lastStop := eq.span.stop }
  have hl₅ : s₅.left = s₅.rest.length := by simp [s₅, s₂, s₁, hl, hs']
  obtain ⟨e', s₆, hpe, he', hL₆⟩ := parseAssign_budget e hwe s₅ ets (semi :: rest) hT rfl hl₅ het
    (fun y hy => hn y (by simp [List.mem_of_mem_tail hy])) (by simp)
    (endsAssign_separator hsemi (by simp [separators])) (by simpa [hsemi] using afterOK_semicolon hae _)
  have hs₆ : s₆.rest = semi :: rest := hL₆.rest_eq
  have hnot : nm.kind ≠ .punct "[" ∧ nm.kind ≠ .punct "{" := by rw [hnm]; simp
  refine ⟨⟨kind, name, none, some e'⟩, { s₆ with rest := rest, left := s₆.left - 1, lastStop := semi.span.stop },
    ?_, by simp [VarDecl.erase, he'], ?_⟩
  · simp only [Parse.parseVarDecl]
    rw [Parse.bind_eq (Parse.advance_eq hs'), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hnot] at h)]
    rw [Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname'), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, reduceCtorEq, heq]
    rw [Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, reduceCtorEq, heq]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₂) rfl (by simp))),
      Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpe, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₆)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, reduceCtorEq, hsemi]
    rw [Parse.bind_eq (endStatement_semi hs₆ hr hsemi)]
    cases kind <;> simp [hkw, VarKind.token, pure, EStateM.pure]
  · exact leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])) (leaves_trans hL₆
        (leaves_advance hs₆ (by rw [hL₆.left_eq, hs₆])))))

/-- `let x: T;`. -/
theorem varDecl_sn {T : Edition} (kind : VarKind) (name : String) (t : TypeExpr)
    (hd : VarDecl.wf T ⟨kind, name, some t, none⟩ = true)
    (s : ParseState) (ts rest : List Token) (hs : s.rest = ts ++ rest)
    (hl : s.left = s.rest.length) (ht : Touching ts (VarDecl.words ⟨kind, name, some t, none⟩))
    (hn : ∀ y ∈ ts.tail, y.newlineBefore = false) (hr : rest ≠ []) :
    ∃ d' s', Parse.parseVarDecl s = .ok d' s' ∧ d'.erase = VarDecl.erase ⟨kind, name, some t, none⟩ ∧
      Leaves s s' rest := by
  simp only [VarDecl.wf, Bool.and_eq_true] at hd
  obtain ⟨⟨hname, hwt⟩, hlet⟩ := hd
  cases kind
  · exact absurd hlet (by decide)
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  simp only [VarDecl.words, VarKind.word_eq] at ht
  obtain ⟨kw, ts₁, rfl, hkw, h₁⟩ := Touching.cons_one (by simpa using ht)
  obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  obtain ⟨colon, ts₃, rfl, hcolon, h₃⟩ := Touching.cons_one (by simpa [punctWord] using h₂)
  obtain ⟨tts, ts₄, rfl, htt, h₄⟩ := Touching.append_split h₃
  obtain ⟨semi, ts₇, rfl, hsemi, h₇⟩ := Touching.cons_one (by simpa [punctWord] using h₄)
  simp [Touching] at h₇; subst h₇
  simp only [VarKind.token] at hkw
  have hs' : s.rest = kw :: nm :: colon :: (tts ++ semi :: rest) := by simpa using hs
  let s₁ := advanced s kw nm (colon :: (tts ++ semi :: rest))
  let s₂ := advanced s₁ nm colon (tts ++ semi :: rest)
  let s₃ : ParseState := { s₂ with rest := tts ++ semi :: rest, left := s₂.left - 1, lastStop := colon.span.stop }
  have hl₃ : s₃.left = s₃.rest.length := by simp [s₃, s₂, s₁, hl, hs']
  obtain ⟨t', s₄, hpt, het', hL₄⟩ := parseType_budget t hwt s₃ tts (semi :: rest) rfl hl₃
    htt.kinds (fun y hy => hn y (by simp [hy])) (by simp) (followsType_eq_semi (.inr hsemi))
  have hs₄ : s₄.rest = semi :: rest := hL₄.rest_eq
  have hnot : nm.kind ≠ .punct "[" ∧ nm.kind ≠ .punct "{" := by rw [hnm]; simp
  refine ⟨⟨.«let», name, some t', none⟩, { s₄ with rest := rest, left := s₄.left - 1, lastStop := semi.span.stop },
    ?_, by simp [VarDecl.erase, het'], ?_⟩
  · simp only [Parse.parseVarDecl]
    rw [Parse.bind_eq (Parse.advance_eq hs'), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hnot] at h)]
    rw [Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname'), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, reduceCtorEq, hcolon]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₂) rfl (by simp))),
      Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpt, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₄)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, reduceCtorEq, hsemi]
    rw [Parse.bind_eq (Parse.peek_eq hs₄)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, reduceCtorEq, hsemi, hkw]
    rw [Parse.bind_eq (endStatement_semi hs₄ hr hsemi)]
    simp [hkw, pure, EStateM.pure]
  · exact leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])) (leaves_trans hL₄
        (leaves_advance hs₄ (by rw [hL₄.left_eq, hs₄])))))

/-- `let x;`. -/
theorem varDecl_nn {T : Edition} (kind : VarKind) (name : String)
    (hd : VarDecl.wf T ⟨kind, name, none, none⟩ = true)
    (s : ParseState) (ts rest : List Token) (hs : s.rest = ts ++ rest)
    (hl : s.left = s.rest.length) (ht : Touching ts (VarDecl.words ⟨kind, name, none, none⟩))
    (hr : rest ≠ []) :
    ∃ d' s', Parse.parseVarDecl s = .ok d' s' ∧ d'.erase = VarDecl.erase ⟨kind, name, none, none⟩ ∧
      Leaves s s' rest := by
  simp only [VarDecl.wf, Bool.and_eq_true] at hd
  obtain ⟨⟨hname, -⟩, hlet⟩ := hd
  cases kind
  · exact absurd hlet (by decide)
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  simp only [VarDecl.words, VarKind.word_eq] at ht
  obtain ⟨kw, ts₁, rfl, hkw, h₁⟩ := Touching.cons_one (by simpa using ht)
  obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  obtain ⟨semi, ts₇, rfl, hsemi, h₇⟩ := Touching.cons_one (by simpa [punctWord] using h₂)
  simp [Touching] at h₇; subst h₇
  simp only [VarKind.token] at hkw
  have hs' : s.rest = kw :: nm :: semi :: rest := by simpa using hs
  let s₁ := advanced s kw nm (semi :: rest)
  let s₂ := advanced s₁ nm semi rest
  obtain ⟨u, r, rfl⟩ := rest_cons hr
  have hnot : nm.kind ≠ .punct "[" ∧ nm.kind ≠ .punct "{" := by rw [hnm]; simp
  refine ⟨⟨.«let», name, none, none⟩, { s₂ with rest := u :: r, left := s₂.left - 1, lastStop := semi.span.stop },
    ?_, rfl, ?_⟩
  · simp only [Parse.parseVarDecl]
    rw [Parse.bind_eq (Parse.advance_eq hs'), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hnot] at h)]
    rw [Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname'), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, reduceCtorEq, hsemi]
    rw [Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, reduceCtorEq, hsemi]
    rw [Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Bool.not_true, Bool.not_false, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, reduceCtorEq, hsemi, hkw]
    rw [Parse.bind_eq (endStatement_semi (s := s₂) rfl (by simp) hsemi)]
    simp [hkw, pure, EStateM.pure]
  · exact leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])))

/-- `const` or `let`, a name, and a type, a value, both or neither. -/
theorem parseVarDecl_reads {T : Edition} (d : VarDecl) (hd : d.wf T = true) :
    ∀ (s : ParseState) (ts rest : List Token), s.target = T → s.rest = ts ++ rest → s.left = s.rest.length →
      Touching ts d.words → (∀ y ∈ ts.tail, y.newlineBefore = false) → rest ≠ [] →
      ∃ d' s', Parse.parseVarDecl s = .ok d' s' ∧ d'.erase = d.erase ∧ Leaves s s' rest := by
  intro s ts rest hT hs hl ht hn hr
  obtain ⟨kind, name, type, init⟩ := d
  rcases type with _ | t <;> rcases init with _ | e
  · exact varDecl_nn kind name hd s ts rest hs hl ht hr
  · exact varDecl_ns kind name e hd s ts rest hT hs hl ht hn hr
  · exact varDecl_sn kind name t hd s ts rest hs hl ht hn hr
  · exact varDecl_ss kind name t e hd s ts rest hT hs hl ht hn hr

end tolean.TypeScript.Syntax
