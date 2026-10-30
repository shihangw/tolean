import tolean.TypeScript.Syntax.RoundTripExpr

/-!
The parser's round trip for statements, on tokens: the parser reads the
tokens that `Syntax/Source.lean` prints for a statement as the same
statement, apart from spans.

The printer writes a statement as lines of words. `Laid ts lines` states that
the tokens `ts` are those lines: the tokens of a word touch, and a line break
comes before the first token of each line after the first. Inside a line, a
line break comes only where the printer puts one, before the `(` of a call
of `async`. `Stmt.wf T fn loop st` is the condition under which
the proofs here show that `parseStatement` reads `st`: the target edition is
`T`, and the statement is in a function if `fn` holds and in a loop if `loop`
holds. An `if` with an `else` needs a branch that does not end with an `if`
without `else`, since that `if` would take the `else`.

`stmts_read` proves the round trip by induction on the parser's fuel. A
statement needs fuel for how deep its statements nest (`Stmt.need`).
-/
namespace tolean.TypeScript.Syntax

open tolean

/-! ### Lines of tokens -/

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
    Touching ts l ∧ ∀ y ∈ ts.tail, NoBreak y := by
  obtain ⟨a, b, rfl, ha, hn, _, hb⟩ := h
  simp [Laid] at hb; subst hb; simpa using ⟨ha, hn⟩

/-- A line, and the lines after it. -/
theorem Laid.cons {ts : List Token} {l : List Word} {ls : List (List Word)} (h : Laid ts (l :: ls)) :
    ∃ a b, ts = a ++ b ∧ Touching a l ∧ (∀ y ∈ a.tail, NoBreak y) ∧
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
      ts.map (·.kind) = t.tokens → (∀ y ∈ ts, NoBreak y) → rest ≠ [] → FollowsType rest →
      ∃ t' s', Parse.parseType (10 * (s.left + 1)) s = .ok t' s' ∧ t'.erase = t.erase ∧ Leaves s s' rest := by
  intro s ts rest hs hl hk hn hr hf
  have h1 := TypeExpr.height_le t
  have h2 : ts.length = t.tokens.length := by rw [← hk, List.length_map]
  have h3 : ts.length ≤ s.left := by rw [hl, hs, List.length_append]; omega
  exact (types_reads _).1 t ht (by omega) s ts rest hs hl hk hn hr hf


/-! ### Declarations of variables -/

theorem readName_ok {s : ParseState} {x u : Token} {r : List Token} {name : String}
    (hs : s.rest = x :: u :: r) (hx : x.kind = .ident name) (hn : name ∉ Parse.refusedNames) :
    Parse.readName s = .ok name (past s x (u :: r)) := by
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
    (hn : ∀ y ∈ ts.tail, NoBreak y) (hr : rest ≠ []) :
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
  let s₁ := past s kw (nm :: (colon :: (tts ++ eq :: (ets ++ semi :: rest))))
  let s₂ := past s₁ nm (colon :: (tts ++ eq :: (ets ++ semi :: rest)))
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
      Bool.false_eq_true, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, hcolon]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₂) rfl (by simp))),
      Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpt, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₄)]
    simp (config := { decide := true }) only [beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      heq]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs₄ (by simp))),
      Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpe, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₆)]
    simp (config := { decide := true }) only [↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Parse.pure_bind,
      hsemi]
    rw [Parse.bind_eq (endStatement_semi hs₆ hr hsemi)]
    cases kind <;> simp [hkw, VarKind.token, pure, EStateM.pure]
  · exact leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])) (leaves_trans hL₄
        (leaves_trans (leaves_advance hs₄ hl₄) (leaves_trans hL₆ (leaves_advance hs₆ (by rw [hL₆.left_eq, hs₆])))))))

/-- `const x = e;` or `let x = e;`. -/
theorem varDecl_ns {T : Edition} (kind : VarKind) (name : String) (e : Expr)
    (hd : VarDecl.wf T ⟨kind, name, none, some e⟩ = true)
    (s : ParseState) (ts rest : List Token) (hT : s.target = T) (hs : s.rest = ts ++ rest)
    (hl : s.left = s.rest.length) (ht : Touching ts (VarDecl.words ⟨kind, name, none, some e⟩))
    (hn : ∀ y ∈ ts.tail, NoBreak y) (hr : rest ≠ []) :
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
  let s₁ := past s kw (nm :: (eq :: (ets ++ semi :: rest)))
  let s₂ := past s₁ nm (eq :: (ets ++ semi :: rest))
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
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, heq]
    rw [Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    simp (config := { decide := true }) only [beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      heq]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₂) rfl (by simp))),
      Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpe, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₆)]
    simp (config := { decide := true }) only [↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Parse.pure_bind,
      hsemi]
    rw [Parse.bind_eq (endStatement_semi hs₆ hr hsemi)]
    cases kind <;> simp [hkw, VarKind.token, pure, EStateM.pure]
  · exact leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])) (leaves_trans hL₆
        (leaves_advance hs₆ (by rw [hL₆.left_eq, hs₆])))))

/-- `let x: T;`. -/
theorem varDecl_sn {T : Edition} (kind : VarKind) (name : String) (t : TypeExpr)
    (hd : VarDecl.wf T ⟨kind, name, some t, none⟩ = true)
    (s : ParseState) (ts rest : List Token) (hs : s.rest = ts ++ rest)
    (hl : s.left = s.rest.length) (ht : Touching ts (VarDecl.words ⟨kind, name, some t, none⟩))
    (hn : ∀ y ∈ ts.tail, NoBreak y) (hr : rest ≠ []) :
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
  let s₁ := past s kw (nm :: (colon :: (tts ++ semi :: rest)))
  let s₂ := past s₁ nm (colon :: (tts ++ semi :: rest))
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
      Bool.false_eq_true, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, hcolon]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₂) rfl (by simp))),
      Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpt, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₄)]
    simp (config := { decide := true }) only [↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Parse.pure_bind,
      hsemi]
    rw [Parse.bind_eq (Parse.peek_eq hs₄)]
    simp (config := { decide := true }) only [↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Parse.pure_bind,
      reduceCtorEq, hsemi, hkw]
    rw [Parse.bind_eq (endStatement_semi hs₄ hr hsemi)]
    simp [pure, EStateM.pure]
  · exact leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
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
  let s₁ := past s kw (nm :: (semi :: rest))
  let s₂ := past s₁ nm (semi :: rest)
  obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  have hnot : nm.kind ≠ .punct "[" ∧ nm.kind ≠ .punct "{" := by rw [hnm]; simp
  refine ⟨⟨.«let», name, none, none⟩, { s₂ with rest := u :: r, left := s₂.left - 1, lastStop := semi.span.stop },
    ?_, rfl, ?_⟩
  · simp only [Parse.parseVarDecl]
    rw [Parse.bind_eq (Parse.advance_eq hs'), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hnot] at h)]
    rw [Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname'), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, ↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Bool.false_eq_true, Parse.pure_bind, Option.isNone_some,
      Option.isNone_none, Bool.and_false, Bool.and_true, hsemi]
    rw [Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    simp (config := { decide := true }) only [↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Parse.pure_bind,
      hsemi]
    rw [Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    simp (config := { decide := true }) only [↓reduceIte, beq_iff_eq,
      TokenKind.punct.injEq, Parse.pure_bind,
      reduceCtorEq, hsemi, hkw]
    rw [Parse.bind_eq (endStatement_semi (s := s₂) rfl (by simp) hsemi)]
    simp [pure, EStateM.pure]
  · exact leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])))

/-- `const` or `let`, a name, and a type, a value, both or neither. -/
theorem parseVarDecl_reads {T : Edition} (d : VarDecl) (hd : d.wf T = true) :
    ∀ (s : ParseState) (ts rest : List Token), s.target = T → s.rest = ts ++ rest → s.left = s.rest.length →
      Touching ts d.words → (∀ y ∈ ts.tail, NoBreak y) → rest ≠ [] →
      ∃ d' s', Parse.parseVarDecl s = .ok d' s' ∧ d'.erase = d.erase ∧ Leaves s s' rest := by
  intro s ts rest hT hs hl ht hn hr
  obtain ⟨kind, name, type, init⟩ := d
  rcases type with _ | t <;> rcases init with _ | e
  · exact varDecl_nn kind name hd s ts rest hs hl ht hr
  · exact varDecl_ns kind name e hd s ts rest hT hs hl ht hn hr
  · exact varDecl_sn kind name t hd s ts rest hs hl ht hn hr
  · exact varDecl_ss kind name t e hd s ts rest hT hs hl ht hn hr

/-! ### Reading a statement -/

/-- `p` reads the tokens of the lines of `st`, followed by any rest, as `st`
apart from spans, and leaves the rest. The state is in a function if `fn`
holds and in a loop if `loop` holds. When `st` ends with an `if` without
`else`, no `else` comes next. -/
def ReadsS (T : Edition) (fn loop : Bool) (p : ParseM Stmt) (st : Stmt) : Prop :=
  ∀ (s : ParseState) (ts rest : List Token), s.target = T → s.inFunction = fn →
    (loop = true → s.loopDepth ≠ 0) → s.rest = ts ++ rest → s.left = s.rest.length →
    Laid ts st.wordLines → rest ≠ [] → (st.openIf = true → ∀ u ∈ rest.head?, u.kind ≠ .keyword "else") →
    ∃ st' s', p s = .ok st' s' ∧ st'.erase = st.erase ∧ Leaves s s' rest

theorem stmt_empty {T : Edition} {fn loop : Bool} (f : Nat) (sp : Span) :
    ReadsS T fn loop (Parse.parseStatement (f + 1)) (.empty sp) := by
  intro s ts rest _ _ _ hs hl ht hr _
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons, List.map_nil] at ht
  obtain ⟨h1, _⟩ := Laid.one ht
  obtain ⟨semi, ts', rfl, hsemi, h'⟩ := Touching.cons_one (by simpa [punctWord] using h1)
  simp [Touching] at h'; subst h'
  have hs' : s.rest = semi :: rest := by simpa using hs
  refine ⟨.empty semi.span, _, ?_, rfl, leaves_advance hs' hl⟩
  simp only [Parse.parseStatement]
  rw [Parse.bind_eq (Parse.peek_eq hs')]
  simp only [hsemi]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs' hr))]
  rfl

theorem stmt_jump {T : Edition} {fn : Bool} (f : Nat) (st : Stmt) (word : String)
    (hst : st.wordLines = [[keywordWord word, punctWord ";"]] ∧ (word = "break" ∨ word = "continue"))
    (hshape : ∀ sp, (if word = "break" then Stmt.breakStmt sp else Stmt.continueStmt sp).erase = st.erase) :
    ReadsS T fn true (Parse.parseStatement (f + 1)) st := by
  intro s ts rest _ _ hL hs hl ht hr _
  rw [hst.1] at ht
  obtain ⟨h1, hn⟩ := Laid.one ht
  obtain ⟨kw, ts', rfl, hkw, h'⟩ := Touching.cons_one (by simpa [keywordWord] using h1)
  obtain ⟨semi, ts'', rfl, hsemi, h''⟩ := Touching.cons_one (by simpa [punctWord] using h')
  simp [Touching] at h''; subst h''
  have hs' : s.rest = kw :: semi :: rest := by simpa using hs
  let s₁ := past s kw (semi :: rest)
  have hd : s₁.loopDepth ≠ 0 := hL rfl
  refine ⟨_, { s₁ with rest := rest, left := s₁.left - 1, lastStop := semi.span.stop }, ?_, hshape ⟨kw.span.start, semi.span.stop⟩,
    leaves_trans (leaves_advance hs' hl) (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))⟩
  simp only [Parse.parseStatement]
  rw [Parse.bind_eq (Parse.peek_eq hs')]
  rcases hst.2 with rfl | rfl <;> simp only [hkw] <;>
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs'))] <;>
    simp [s₁, hd, Parse.peek_eq (s := s₁) rfl, hsemi, Token.isAnyIdent, Token.isKeyword, hkw,
      endStatement_semi (s := s₁) rfl hr hsemi, Parse.spanFrom_eq, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, pure, EStateM.pure]


theorem stmt_return_none {T : Edition} {loop : Bool} (f : Nat) (sp : Span) :
    ReadsS T true loop (Parse.parseStatement (f + 1)) (.returnStmt sp none) := by
  intro s ts rest _ hF _ hs hl ht hr _
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons, List.map_nil] at ht
  obtain ⟨h1, hn⟩ := Laid.one ht
  obtain ⟨kw, ts', rfl, hkw, h'⟩ := Touching.cons_one (by simpa [keywordWord] using h1)
  obtain ⟨semi, ts'', rfl, hsemi, h''⟩ := Touching.cons_one (by simpa [punctWord] using h')
  simp [Touching] at h''; subst h''
  have hs' : s.rest = kw :: semi :: rest := by simpa using hs
  let s₁ := past s kw (semi :: rest)
  have hF₁ : s₁.inFunction = true := hF
  refine ⟨.returnStmt ⟨kw.span.start, semi.span.stop⟩ none,
    { s₁ with rest := rest, left := s₁.left - 1, lastStop := semi.span.stop }, ?_, rfl,
    leaves_trans (leaves_advance hs' hl) (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))⟩
  simp only [Parse.parseStatement]
  rw [Parse.bind_eq (Parse.peek_eq hs')]
  simp only [hkw]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs'))]
  have hg : (get : ParseM ParseState) s₁ = .ok s₁ s₁ := rfl
  rw [Parse.bind_eq hg]
  simp only [hF₁, ↓reduceIte, Parse.pure_bind]
  rw [Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
  simp only [Token.isPunct, hsemi, beq_self_eq_true, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Parse.pure_bind]
  rw [Parse.bind_eq (endStatement_semi (s := s₁) rfl hr hsemi), Parse.bind_eq (Parse.spanFrom_eq _ _)]
  simp [hF₁, pure, EStateM.pure]

/-- The first word of an expression has tokens: no `lineBreak` starts it. -/
theorem Expr.firstWord : ∀ e : Expr, ∃ w ws, e.words = w :: ws ∧ w ≠ []
  | .ident _ n => ⟨_, _, by simp only [Expr.words]; exact rfl, by simp [identWord]⟩
  | .number _ t => ⟨_, _, by simp only [Expr.words]; exact rfl, by simp⟩
  | .bigint _ t => ⟨_, _, by simp only [Expr.words]; exact rfl, by simp⟩
  | .string _ v => ⟨_, _, by simp only [Expr.words]; exact rfl, by simp⟩
  | .bool _ b => ⟨_, _, by simp only [Expr.words]; exact rfl, by simp [keywordWord]⟩
  | .null _ => ⟨_, _, by simp only [Expr.words]; exact rfl, by simp [keywordWord]⟩
  | .array _ es => ⟨_, _, by simp only [Expr.words, enclose]; exact rfl, by simp [punctWord]⟩
  | .object _ ps => ⟨_, _, by simp only [Expr.words, enclose]; exact rfl, by simp [punctWord]⟩
  | .paren _ i => ⟨_, _, by simp only [Expr.words]; exact rfl, by simp [punctWord]⟩
  | .unary _ op a => by
    obtain ⟨k, hk, _⟩ := unaryOp_symbol op
    exact ⟨_, _, by simp only [Expr.words]; exact rfl, by simp [hk]⟩
  | .prefix _ op a => ⟨_, _, by simp only [Expr.words]; exact rfl, by simp [punctWord]⟩
  | .member _ o _ => by
    obtain ⟨w, ws, h, hw⟩ := Expr.firstWord o
    exact ⟨w, _, by simp only [Expr.words, h, List.cons_append]; exact rfl, hw⟩
  | .index _ o _ => by
    obtain ⟨w, ws, h, hw⟩ := Expr.firstWord o
    exact ⟨w, _, by simp only [Expr.words, h, List.cons_append]; exact rfl, hw⟩
  | .call _ c _ => by
    obtain ⟨w, ws, h, hw⟩ := Expr.firstWord c
    exact ⟨w, _, by simp only [Expr.words, h, List.cons_append]; exact rfl, hw⟩
  | .postfix _ _ a => by
    obtain ⟨w, ws, h, hw⟩ := Expr.firstWord a
    exact ⟨w, _, by simp only [Expr.words, h, List.cons_append]; exact rfl, hw⟩
  | .binary _ _ l _ => by
    obtain ⟨w, ws, h, hw⟩ := Expr.firstWord l
    exact ⟨w, _, by simp only [Expr.words, h, List.cons_append]; exact rfl, hw⟩
  | .cond _ t _ _ => by
    obtain ⟨w, ws, h, hw⟩ := Expr.firstWord t
    exact ⟨w, _, by simp only [Expr.words, h, List.cons_append]; exact rfl, hw⟩
  | .assign _ _ t _ => by
    obtain ⟨w, ws, h, hw⟩ := Expr.firstWord t
    exact ⟨w, _, by simp only [Expr.words, h, List.cons_append]; exact rfl, hw⟩

/-- No line break comes before the token after a word of one token, when a
word with tokens follows that word. -/
theorem Touching.after_one {k : TokenKind} {v : Word} {ws : List Word} {x₀ x : Token} {r : List Token}
    (h : Touching (x₀ :: x :: r) ([k] :: v :: ws)) (hv : v ≠ []) : x.newlineBefore = false := by
  obtain ⟨a, b, hab, ha, hp, _⟩ := h
  match a, ha with
  | [y], _ =>
    simp at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact Placed.next (by simp) hv hp

theorem stmt_return_some {T : Edition} {loop : Bool} (f : Nat) (sp : Span) (e : Expr)
    (he : e.wfAt T .assign = true) (ha : e.afterOK [.punct ";"] = true) :
    ReadsS T true loop (Parse.parseStatement (f + 1)) (.returnStmt sp (some e)) := by
  intro s ts rest hT hF _ hs hl ht hr _
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons, List.map_nil] at ht
  obtain ⟨h1, hn⟩ := Laid.one ht
  obtain ⟨kw, ts', rfl, hkw, h'⟩ := Touching.cons_one (by simpa [keywordWord] using h1)
  obtain ⟨ets, ts'', rfl, het, h''⟩ := Touching.append_split h'
  obtain ⟨semi, ts₃, rfl, hsemi, h₃⟩ := Touching.cons_one (by simpa [punctWord] using h'')
  simp [Touching] at h₃; subst h₃
  obtain ⟨x, ets', rfl, hx⟩ := Touching.head het
  have hs' : s.rest = kw :: x :: (ets' ++ semi :: rest) := by simpa using hs
  let s₁ := past s kw (x :: (ets' ++ semi :: rest))
  have hF₁ : s₁.inFunction = true := hF
  have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs']
  obtain ⟨w₀, ws₀, hw₀, hne₀⟩ := Expr.firstWord e
  have h1' : Touching (kw :: x :: (ets' ++ [semi])) ([.keyword "return"] :: w₀ :: (ws₀ ++ [punctWord ";"])) := by
    simpa [keywordWord, hw₀] using h1
  -- `return` reads no value after a line break, as ECMA-262 states.
  have hxn : x.newlineBefore = false := Touching.after_one h1' hne₀
  have hx1 : x.kind ≠ .punct ";" := fun h => by rw [h] at hx; simp [startsExpr] at hx
  have hx2 : x.kind ≠ .punct "}" := fun h => by rw [h] at hx; simp [startsExpr] at hx
  have hx3 : x.kind ≠ .eof := fun h => by rw [h] at hx; simp [startsExpr] at hx
  obtain ⟨e', s₂, hp, he', hL₂⟩ := parseExpression_budget e he s₁ (x :: ets') (semi :: rest) hT (by simp [s₁])
    hl₁ het (fun y hy => hn y (by simp at hy ⊢; simp [hy])) (by simp)
    ⟨endsAssign_separator hsemi (by simp [separators]), fun u hu => by
      simp at hu; subst hu; rw [hsemi]; exact punct_ne (by decide)⟩
    (by simpa [hsemi] using afterOK_semicolon ha _)
  have hs₂ : s₂.rest = semi :: rest := hL₂.rest_eq
  refine ⟨.returnStmt ⟨kw.span.start, semi.span.stop⟩ (some e'),
    { s₂ with rest := rest, left := s₂.left - 1, lastStop := semi.span.stop }, ?_, by simp [Stmt.erase, he'],
    leaves_trans (leaves_advance hs' hl) (leaves_trans hL₂ (leaves_advance hs₂ (by rw [hL₂.left_eq, hs₂])))⟩
  simp only [Parse.parseStatement]
  rw [Parse.bind_eq (Parse.peek_eq hs')]
  simp only [hkw]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs'))]
  have hg : (get : ParseM ParseState) s₁ = .ok s₁ s₁ := rfl
  rw [Parse.bind_eq hg]
  simp only [hF₁, ↓reduceIte, Parse.pure_bind]
  rw [Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
  have hb1 : (x.kind == .punct ";") = false := by simp [hx1]
  have hb2 : (x.kind == .punct "}") = false := by simp [hx2]
  have hb3 : (x.kind == .eof) = false := by simp [hx3]
  simp only [Token.isPunct, Token.isEof, hb1, hb2, hb3, hxn, Bool.or_false, Bool.not_false, ↓reduceIte]
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hp, Parse.pure_bind, Parse.bind_eq (endStatement_semi hs₂ hr hsemi),
    Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl


/-- `parseStatement` hands an expression statement to `parseExpressionStatement`. -/
theorem parseStatement_expr {f : Nat} {s : ParseState} {x : Token} {r : List Token} (hs : s.rest = x :: r)
    (hx : startsExpr x.kind = true) (hk : startsExprStmt (some x.kind) = true) :
    Parse.parseStatement (f + 1) s = Parse.parseExpressionStatement f s := by
  simp only [Parse.parseStatement]
  rw [Parse.bind_eq (Parse.peek_eq hs)]
  generalize x.kind = k at hx hk ⊢
  cases k with
  | ident n =>
    have hn : n ≠ "let" := by rintro rfl; simp [startsExprStmt] at hk
    simp [hn]
  | keyword w =>
    simp [startsExprStmt] at hk
    rcases hk with (((rfl | rfl) | rfl) | rfl) | rfl <;> rfl
  | punct p =>
    have h1 : p ≠ "{" := by rintro rfl; simp [startsExprStmt] at hk
    have h2 : p ≠ ";" := by rintro rfl; simp [startsExpr] at hx
    simp [h1, h2]
  | _ => rfl


/-- An expression and its `;`. -/
theorem stmt_expr {T : Edition} {fn loop : Bool} (g : Nat) (sp : Span) (e : Expr)
    (hw : (Stmt.exprStmt sp e).wf T fn loop = true) :
    ReadsS T fn loop (Parse.parseStatement (g + 1 + 1)) (.exprStmt sp e) := by
  intro s ts rest hT _ _ hs hl ht hr _
  simp only [Stmt.wf, Bool.and_eq_true] at hw
  obtain ⟨⟨he, ha⟩, hk⟩ := hw
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons, List.map_nil] at ht
  obtain ⟨h1, hn⟩ := Laid.one ht
  obtain ⟨ets, ts', rfl, het, h'⟩ := Touching.append_split h1
  obtain ⟨semi, ts'', rfl, hsemi, h''⟩ := Touching.cons_one (by simpa [punctWord] using h')
  simp [Touching] at h''; subst h''
  obtain ⟨x, ets', rfl, hx⟩ := Touching.head het
  have hxk : startsExprStmt (some x.kind) = true := by
    have : e.tokens.head? = some x.kind := by
      have := het.kinds; simp only [Expr.tokens, ← this]; simp
    rw [← this]; exact hk
  have hs' : s.rest = x :: (ets' ++ semi :: rest) := by simpa using hs
  obtain ⟨e', s₂, hp, he', hL₂⟩ := parseExpression_budget e he s (x :: ets') (semi :: rest) hT (by simp [hs'])
    hl het (fun y hy => hn y (by simp at hy ⊢; simp [hy])) (by simp)
    ⟨endsAssign_separator hsemi (by simp [separators]), fun u hu => by
      simp at hu; subst hu; rw [hsemi]; exact punct_ne (by decide)⟩
    (by simpa [hsemi] using afterOK_semicolon ha _)
  have hs₂ : s₂.rest = semi :: rest := hL₂.rest_eq
  refine ⟨.exprStmt ⟨x.span.start, semi.span.stop⟩ e',
    { s₂ with rest := rest, left := s₂.left - 1, lastStop := semi.span.stop }, ?_, by simp [Stmt.erase, he'],
    leaves_trans hL₂ (leaves_advance hs₂ (by rw [hL₂.left_eq, hs₂]))⟩
  rw [parseStatement_expr hs' hx hxk]
  simp only [Parse.parseExpressionStatement]
  rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hp,
    Parse.bind_eq (endStatement_semi hs₂ hr hsemi), Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl

/-- A declaration of a variable. -/
theorem stmt_varDecl {T : Edition} {fn loop : Bool} (f : Nat) (sp : Span) (d : VarDecl)
    (hw : (Stmt.varDecl sp d).wf T fn loop = true) :
    ReadsS T fn loop (Parse.parseStatement (f + 1)) (.varDecl sp d) := by
  intro s ts rest hT _ _ hs hl ht hr _
  simp only [Stmt.wf] at hw
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons, List.map_nil] at ht
  obtain ⟨h1, hn⟩ := Laid.one ht
  obtain ⟨d', s', hp, hd', hL⟩ := parseVarDecl_reads d hw s ts rest hT hs hl h1 hn hr
  have h1' := h1
  simp only [VarDecl.words, VarKind.word_eq] at h1'
  obtain ⟨kw, ts', rfl, hkw, _⟩ := Touching.cons_one (by simpa using h1')
  have hs' : s.rest = kw :: (ts' ++ rest) := by simpa using hs
  refine ⟨.varDecl ⟨kw.span.start, s'.lastStop⟩ d', s', ?_, by simp [Stmt.erase, hd'], hL⟩
  simp only [Parse.parseStatement]
  rw [Parse.bind_eq (Parse.peek_eq hs')]
  rcases hk : d.kind <;> rw [hk] at hkw <;> simp only [VarKind.token] at hkw <;> simp only [hkw] <;>
    rw [Parse.bind_eq hp, Parse.bind_eq (Parse.spanFrom_eq _ _)] <;> rfl


theorem Laid.kinds : ∀ {ts : List Token} {ls : List (List Word)}, Laid ts ls → ts.map (·.kind) = ls.flatten.flatten
  | ts, [], h => by simp [Laid] at h; simp [h]
  | _, l :: ls, ⟨a, b, rfl, ha, _, _, hb⟩ => by simp [ha.kinds, Laid.kinds hb]

/-- What a well-formed statement starts with. -/
def StartsStmt (k : TokenKind) (decl : Bool) : Prop :=
  k ≠ .punct "}" ∧ k ≠ .eof ∧ k ≠ .keyword "else" ∧ (decl = false → k ≠ .keyword "const" ∧ k ≠ .ident "let")

theorem Stmt.first {T : Edition} {fn loop : Bool} (st : Stmt) (hw : st.wf T fn loop = true) :
    ∃ k, st.wordLines.flatten.flatten.head? = some k ∧ StartsStmt k st.isDecl := by
  cases st with
  | varDecl sp d =>
    refine ⟨d.kind.token, ?_, ?_⟩
    · simp [Stmt.wordLines, Stmt.lines, VarDecl.words, VarKind.word_eq]
    · cases d.kind <;> simp [StartsStmt, VarKind.token, Stmt.isDecl]
  | exprStmt sp e =>
    simp only [Stmt.wf, Bool.and_eq_true] at hw
    obtain ⟨k, hk, hs⟩ := Expr.first e
    have hk' : startsExprStmt (some k) = true := hk ▸ hw.2
    refine ⟨k, ?_, ?_⟩
    · simp only [Stmt.wordLines, Stmt.lines, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.flatten_append]
      exact head_append_of hk
    · refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun _ => ⟨fun h => ?_, fun h => ?_⟩⟩ <;> subst h <;>
        simp [startsExpr, startsExprStmt] at hs hk'
  | returnStmt sp v =>
    refine ⟨.keyword "return", ?_, by simp [StartsStmt]⟩
    cases v <;> simp [Stmt.wordLines, Stmt.lines, keywordWord]
  | ifStmt sp test t e =>
    refine ⟨.keyword "if", ?_, by simp [StartsStmt]⟩
    cases e <;> simp [Stmt.wordLines, Stmt.lines, keywordWord]
  | forOfStmt _ _ _ _ _ => exact ⟨.keyword "for", by simp [Stmt.wordLines, Stmt.lines, keywordWord], by simp [StartsStmt]⟩
  | whileStmt _ _ _ => exact ⟨.keyword "while", by simp [Stmt.wordLines, Stmt.lines, keywordWord], by simp [StartsStmt]⟩
  | block _ _ => exact ⟨.punct "{", by simp [Stmt.wordLines, Stmt.lines, punctWord], by simp [StartsStmt]⟩
  | breakStmt _ => exact ⟨.keyword "break", by simp [Stmt.wordLines, Stmt.lines, keywordWord], by simp [StartsStmt]⟩
  | continueStmt _ =>
    exact ⟨.keyword "continue", by simp [Stmt.wordLines, Stmt.lines, keywordWord], by simp [StartsStmt]⟩
  | empty _ => exact ⟨.punct ";", by simp [Stmt.wordLines, Stmt.lines, punctWord], by simp [StartsStmt]⟩

/-- The first token of a statement's tokens. -/
theorem Laid.first {T : Edition} {fn loop : Bool} {st : Stmt} {ts : List Token} (hw : st.wf T fn loop = true)
    (h : Laid ts st.wordLines) : ∃ x ts', ts = x :: ts' ∧ StartsStmt x.kind st.isDecl := by
  obtain ⟨k, hk, hs⟩ := Stmt.first st hw
  have hk' : (ts.map (·.kind)).head? = some k := by rw [h.kinds]; exact hk
  cases ts with
  | nil => simp at hk'
  | cons x ts' => simp at hk'; exact ⟨x, ts', rfl, hk' ▸ hs⟩

/-- The body of `if`, `else`, `for` or `while`. -/
theorem parseBranch_reads {T : Edition} {fn loop : Bool} (g : Nat) (st : Stmt) (hd : st.isDecl = false)
    (hw : st.wf T fn loop = true) (h : ReadsS T fn loop (Parse.parseStatement g) st) :
    ReadsS T fn loop (Parse.parseBranch (g + 1)) st := by
  intro s ts rest hT hF hL hs hl ht hr he
  obtain ⟨x, ts', rfl, hx⟩ := Laid.first hw ht
  obtain ⟨st', s', hp, hst, hL'⟩ := h s _ rest hT hF hL hs hl ht hr he
  refine ⟨st', s', ?_, hst, hL'⟩
  obtain ⟨-, -, -, hx'⟩ := hx
  obtain ⟨h1, h2⟩ := hx' hd
  simp only [Parse.parseBranch]
  rw [Parse.bind_eq (Parse.peek_eq (by simpa using hs))]
  have : Parse.refuseDeclaration x s = .ok () s := by
    simp [Parse.refuseDeclaration, Token.isKeyword, Token.isIdent, h1, h2, pure, EStateM.pure]
  rw [Parse.bind_eq this]
  exact hp

/-! ### Blocks -/

theorem Stmt.linesOf_wordLines (ss : List Stmt) (d : Nat) :
    (Stmt.linesOf d ss).map Prod.snd = (ss.map Stmt.wordLines).flatten := by
  induction ss with
  | nil => rfl
  | cons st ss ih =>
    simp only [Stmt.linesOf, List.map_append, ih, List.map_cons, List.flatten_cons]
    rw [Stmt.lines_words]; rfl

/-- After the statements of a block comes the next statement or the `}`, and no `else`. -/
theorem next_not_else {T : Edition} {fn loop : Bool} {c : Token} {rest : List Token} (hc : c.kind = .punct "}") :
    ∀ {body : List Stmt} {b : List Token}, (∀ st ∈ body, st.wf T fn loop = true) →
      Laid b (body.map Stmt.wordLines).flatten → ∀ u ∈ (b ++ c :: rest).head?, u.kind ≠ .keyword "else"
  | [], b, _, hb => by
    simp [Laid] at hb; subst hb; intro u hu; simp at hu; subst hu; rw [hc]; simp
  | st :: body, b, hw, hb => by
    obtain ⟨a, b', rfl, ha, _, _⟩ := Laid.append (by simpa using hb)
    obtain ⟨x, a', rfl, hx⟩ := Laid.first (hw st (by simp)) ha
    intro u hu; simp at hu; subst hu; exact hx.2.2.1

theorem Laid.length_le {T : Edition} {fn loop : Bool} :
    ∀ {body : List Stmt} {ts : List Token}, (∀ st ∈ body, st.wf T fn loop = true) →
      Laid ts (body.map Stmt.wordLines).flatten → body.length ≤ ts.length
  | [], _, _, _ => by simp
  | st :: body, ts, hw, h => by
    obtain ⟨a, b, rfl, ha, hb, _⟩ := Laid.append (by simpa using h)
    obtain ⟨x, a', rfl, _⟩ := Laid.first (hw st (by simp)) ha
    have := Laid.length_le (fun s hs => hw s (by simp [hs])) hb
    simp; omega

/-- The loop that `Parse.blockStep p` runs reads items, the lines of each after the lines of the one
before, which a `}` follows. `Inv` holds in each state between two items. `hread` states that `p` reads
an item `x`, which the lines of the items `later` follow, and that a token other than `}` and the end of
the file starts `x`. -/
theorem blockStep_loop {α : Type} {p : ParseM α} {erase : α → α} {lines : α → List (List Word)}
    {Inv : ParseState → Prop} (hInv : ∀ {s s' : ParseState} {r : List Token}, Inv s → Leaves s s' r → Inv s')
    {items : List α} {rest : List Token} {c : Token}
    (hread : ∀ x ∈ items, ∀ later : List α, (∀ y ∈ later, y ∈ items) →
      ∀ (s : ParseState) (a b : List Token), Inv s → s.rest = a ++ (b ++ c :: rest) →
        s.left = s.rest.length → Laid a (lines x) → Laid b (later.map lines).flatten →
        ∃ x' s' k a', a = k :: a' ∧ k.kind ≠ .punct "}" ∧ k.kind ≠ .eof ∧
          p s = .ok x' s' ∧ erase x' = erase x ∧ Leaves s s' (b ++ c :: rest))
    (hc : c.kind = .punct "}") :
    ∀ (later : List α), (∀ y ∈ later, y ∈ items) → ∀ (fuel : Nat) (acc : Array α) (s : ParseState)
      (ts : List Token), later.length < fuel → Inv s → s.rest = ts ++ c :: rest → s.left = s.rest.length →
      Laid ts (later.map lines).flatten →
      ∃ res s', Parse.iterate fuel acc (Parse.blockStep p) s = .ok res s' ∧
        res.toList.map erase = (acc.toList ++ later).map erase ∧ Leaves s s' (c :: rest) := by
  intro later
  induction later with
  | nil =>
    intro _ fuel acc s ts hlen _ hs hl ht
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    simp [Laid] at ht; subst ht
    have hs' : s.rest = c :: rest := by simpa using hs
    refine ⟨acc, s, Parse.iterate_false ?_, by simp, Leaves.refl hs' (by simp [hl, hs'])⟩
    simp only [Parse.blockStep]
    rw [Parse.bind_eq (Parse.peek_eq hs')]
    simp [Token.isPunct, hc, pure, EStateM.pure]
  | cons x later ih =>
    intro hsub fuel acc s ts hlen hI hs hl ht
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    obtain ⟨a, b, rfl, ha, hb, _⟩ := Laid.append (by simpa using ht)
    obtain ⟨x', s₁, k, a', rfl, hk1, hk2, hp, he, hL₁⟩ := hread x (hsub x (by simp)) later
      (fun y hy => hsub y (by simp [hy])) s _ b hI (by simpa using hs) hl ha hb
    have hs' : s.rest = k :: (a' ++ (b ++ c :: rest)) := by simpa using hs
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL₁.left_eq, hL₁.rest_eq]
    obtain ⟨res, s', hit, he', hL'⟩ := ih (fun y hy => hsub y (by simp [hy])) f' (acc.push x') s₁ b
      (by simp at hlen; omega) (hInv hI hL₁) hL₁.rest_eq hl₁ hb
    refine ⟨res, s', ?_, by rw [he']; simp [he], leaves_trans hL₁ hL'⟩
    rw [Parse.iterate_true (acc' := acc.push x') (s' := s₁)]
    · exact hit
    · have hb1 : (k.kind == .punct "}") = false := by simp [hk1]
      have hb2 : (k.kind == .eof) = false := by simp [hk2]
      simp only [Parse.blockStep]
      rw [Parse.bind_eq (Parse.peek_eq hs')]
      simp only [Token.isPunct, Token.isEof, hb1, hb2, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind]
      rw [Parse.bind_eq hp]
      rfl

/-- The loop of `parseBlock` reads the statements of a block, which a `}` follows. -/
theorem block_loop {T : Edition} {fn loop : Bool} {p : ParseM Stmt} :
    ∀ (body : List Stmt) (fuel : Nat) (acc : Array Stmt) (s : ParseState) (ts rest : List Token) (c : Token),
      (∀ st ∈ body, st.wf T fn loop = true ∧ ReadsS T fn loop p st) → body.length < fuel →
      s.target = T → s.inFunction = fn → (loop = true → s.loopDepth ≠ 0) →
      s.rest = ts ++ c :: rest → c.kind = .punct "}" → s.left = s.rest.length →
      Laid ts (body.map Stmt.wordLines).flatten →
      ∃ res s', Parse.iterate fuel acc (Parse.blockStep p) s = .ok res s' ∧
        res.toList.map Stmt.erase = (acc.toList ++ body).map Stmt.erase ∧ Leaves s s' (c :: rest) := by
  intro body fuel acc s ts rest c hrd hlen hT hF hL hs hc hl ht
  refine blockStep_loop (Inv := fun s => s.target = T ∧ s.inFunction = fn ∧ (loop = true → s.loopDepth ≠ 0))
    (fun hI hL' => ⟨hL'.target_eq.trans hI.1, hL'.inFunction_eq.trans hI.2.1,
      fun h => by rw [hL'.loopDepth_eq]; exact hI.2.2 h⟩) ?_ hc body (fun y hy => hy) fuel acc s ts hlen
    ⟨hT, hF, hL⟩ hs hl ht
  intro st hst later hlater s a b hI hs hl ha hb
  obtain ⟨hw, hrs⟩ := hrd st hst
  obtain ⟨k, a', rfl, hk⟩ := Laid.first hw ha
  obtain ⟨h1, h2, -, -⟩ := hk
  obtain ⟨st', s₁, hp, he, hL₁⟩ := hrs s (k :: a') (b ++ c :: rest) hI.1 hI.2.1 hI.2.2 hs hl ha (by simp)
    (fun _ => next_not_else hc (fun t ht => (hrd t (hlater t ht)).1) hb)
  exact ⟨st', s₁, k, a', rfl, h1, h2, hp, he, hL₁⟩

theorem Stmt.eraseAll_eq (ss : List Stmt) : Stmt.eraseAll ss = ss.map Stmt.erase := by
  induction ss with
  | nil => rfl
  | cons st ss ih => simp [Stmt.eraseAll, ih]

/-- `{`, the statements of a block, and `}`. -/
theorem parseBlock_reads {T : Edition} {fn loop : Bool} (g : Nat) (sp : Span) (body : List Stmt)
    (hrd : ∀ st ∈ body, st.wf T fn loop = true ∧ ReadsS T fn loop (Parse.parseStatement g) st) :
    ReadsS T fn loop (Parse.parseBlock (g + 1)) (.block sp body) := by
  intro s ts rest hT hF hL hs hl ht hr _
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons, List.map_append, Stmt.linesOf_wordLines,
    List.map_nil] at ht
  obtain ⟨a, b, rfl, ha, _, _, hb⟩ := Laid.cons ht
  obtain ⟨lb, a', rfl, hlb, h'⟩ := Touching.cons_one (by simpa [punctWord] using ha)
  simp [Touching] at h'; subst h'
  obtain ⟨b₁, b₂, rfl, hb₁, hb₂, _⟩ := Laid.append hb
  obtain ⟨hrb, _⟩ := Laid.one hb₂
  obtain ⟨rb, b₂', rfl, hrbk, h''⟩ := Touching.cons_one (by simpa [punctWord] using hrb)
  simp [Touching] at h''; subst h''
  have hs' : s.rest = lb :: (b₁ ++ rb :: rest) := by simpa using hs
  let s₁ : ParseState := { s with rest := b₁ ++ rb :: rest, left := s.left - 1, lastStop := lb.span.stop }
  have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs']
  have hlen := Laid.length_le (fun st h => (hrd st h).1) hb₁
  obtain ⟨res, s₂, hit, he, hL₂⟩ := block_loop body (10 * (s₁.left + 1)) #[] s₁ b₁ rest rb hrd
    (by have : s₁.left = b₁.length + rest.length + 1 := by simp [s₁, hl, hs']; omega
        omega) hT hF hL rfl hrbk hl₁ hb₁
  have hs₂ : s₂.rest = rb :: rest := hL₂.rest_eq
  refine ⟨.block ⟨lb.span.start, rb.span.stop⟩ res.toList,
    { s₂ with rest := rest, left := s₂.left - 1, lastStop := rb.span.stop }, ?_, ?_,
    leaves_trans (leaves_advance hs' hl) (leaves_trans hL₂ (leaves_advance hs₂ (by rw [hL₂.left_eq, hs₂])))⟩
  · simp only [Parse.parseBlock]
    rw [Parse.bind_eq (Parse.expectPunct_ok hs' (by simp) hlb), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_eq hit, Parse.bind_eq (Parse.expectPunct_ok hs₂ hr hrbk), Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · simpa [Stmt.erase, Stmt.eraseAll_eq] using he

/-- `parseStatement` reads a block with `parseBlock`. -/
theorem stmt_block {T : Edition} {fn loop : Bool} (f : Nat) (sp : Span) (body : List Stmt)
    (h : ReadsS T fn loop (Parse.parseBlock f) (.block sp body)) :
    ReadsS T fn loop (Parse.parseStatement (f + 1)) (.block sp body) := by
  intro s ts rest hT hF hL hs hl ht hr he
  obtain ⟨st', s', hp, hst, hL'⟩ := h s ts rest hT hF hL hs hl ht hr he
  refine ⟨st', s', ?_, hst, hL'⟩
  simp only [Stmt.wordLines, Stmt.lines] at ht
  obtain ⟨a, b, rfl, ha, _⟩ := Laid.cons ht
  obtain ⟨lb, a', rfl, hlb, _⟩ := Touching.cons_one (by simpa [punctWord] using ha)
  simp only [Parse.parseStatement]
  rw [Parse.bind_eq (Parse.peek_eq (by simpa using hs))]
  simp only [hlb]
  exact hp

theorem afterOK_closer {e : Expr} (h : e.afterOK [.punct ")"] = true) (x : List TokenKind) :
    e.afterOK (.punct ")" :: x) = true := by
  rw [Expr.afterOK_congr e (a := .punct ")" :: x) (b := [.punct ")"]) ⟨rfl, by simp [closesKinds]⟩]; exact h

/-- A `)` ends an expression. -/
theorem EndsExpr.closer {rp : Token} {r : List Token} (h : rp.kind = .punct ")") : EndsExpr (rp :: r) :=
  ⟨endsAssign_separator h (by simp [separators]), fun u hu => by
    simp at hu; subst hu; rw [h]; exact punct_ne (by decide)⟩


/-- The first line of `if ( test )` or `while ( test )`: the keyword, `(`, the test and `)`. -/
theorem Touching.keywordParen {ts : List Token} {kw : String} {test : Expr}
    (h : Touching ts (keywordWord kw :: punctWord "(" :: test.words ++ [punctWord ")"])) :
    ∃ k lp tts rp, ts = k :: lp :: (tts ++ [rp]) ∧ k.kind = .keyword kw ∧ lp.kind = .punct "(" ∧
      Touching tts test.words ∧ rp.kind = .punct ")" := by
  obtain ⟨k, ts₁, rfl, hk, h₁⟩ := Touching.cons_one (by simpa [keywordWord] using h)
  obtain ⟨lp, ts₂, rfl, hlp, h₂⟩ := Touching.cons_one (by simpa [punctWord] using h₁)
  obtain ⟨tts, ts₃, rfl, htt, h₃⟩ := Touching.append_split h₂
  obtain ⟨rp, ts₄, rfl, hrp, h₄⟩ := Touching.cons_one (by simpa [punctWord] using h₃)
  simp [Touching] at h₄; subst h₄
  exact ⟨k, lp, tts, rp, rfl, hk, hlp, htt, hrp⟩

/-- `if ( test )` and a branch, which `parseBranch` reads, with no `else`. -/
theorem stmt_if_none {T : Edition} {fn loop : Bool} (g : Nat) (sp : Span) (test : Expr) (t : Stmt)
    (hw : (Stmt.ifStmt sp test t none).wf T fn loop = true)
    (ht : ReadsS T fn loop (Parse.parseBranch (g + 1)) t) :
    ReadsS T fn loop (Parse.parseStatement (g + 1 + 1)) (.ifStmt sp test t none) := by
  intro s ts rest hT hF hL hs hl hlaid hr hopen
  simp only [Stmt.wf, Bool.and_eq_true, Expr.wfParen] at hw
  obtain ⟨⟨⟨hwe, hae⟩, -⟩, -⟩ := hw
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons] at hlaid
  rw [Stmt.lines_words t 1] at hlaid
  obtain ⟨a, b, rfl, ha, hna, _, hb⟩ := Laid.cons hlaid
  obtain ⟨k, lp, tts, rp, rfl, hk, hlp, htt, hrp⟩ := Touching.keywordParen ha
  have hs' : s.rest = k :: lp :: (tts ++ rp :: (b ++ rest)) := by simpa using hs
  let s₁ := past s k (lp :: (tts ++ rp :: (b ++ rest)))
  let s₂ : ParseState := { s₁ with rest := tts ++ rp :: (b ++ rest), left := s₁.left - 1, lastStop := lp.span.stop }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁, hl, hs']
  obtain ⟨test', s₃, hpt, het, hL₃⟩ := parseExpression_budget test hwe s₂ tts (rp :: (b ++ rest)) hT rfl hl₂ htt
    (fun y hy => hna y (by simp [List.mem_of_mem_tail hy])) (by simp) (EndsExpr.closer hrp)
    (by simpa [hrp] using afterOK_closer hae _)
  have hs₃ : s₃.rest = rp :: (b ++ rest) := hL₃.rest_eq
  let s₄ : ParseState := { s₃ with rest := b ++ rest, left := s₃.left - 1, lastStop := rp.span.stop }
  have hl₄ : s₄.left = s₄.rest.length := by simp [s₄, hL₃.left_eq]
  obtain ⟨t', s₅, hpb, het', hL₅⟩ := ht s₄ b rest (hL₃.target_eq.trans hT) (hL₃.inFunction_eq.trans hF)
    (fun h => by simp only [s₄]; rw [hL₃.loopDepth_eq]; exact hL h) rfl hl₄ hb hr (fun _ => hopen rfl)
  obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  have hu : u.kind ≠ .keyword "else" := hopen rfl u rfl
  have hs₅ : s₅.rest = u :: r := hL₅.rest_eq
  refine ⟨.ifStmt ⟨k.span.start, s₅.lastStop⟩ test' t' none, s₅, ?_,
    by simp [Stmt.erase, Stmt.eraseOpt, het, het'],
    leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans hL₃ (leaves_trans (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃])) hL₅)))⟩
  simp only [Parse.parseStatement]
  rw [Parse.bind_eq (Parse.peek_eq hs')]
  simp only [hk]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')),
    Parse.bind_eq (Parse.expectPunct_ok (s := s₁) rfl (by simp) hlp), Parse.bind_eq (Parse.budget_eq _),
    Parse.bind_eq hpt, Parse.bind_eq (Parse.expectPunct_ok hs₃ (by simp [hr]) hrp), Parse.bind_eq hpb,
    Parse.bind_eq (Parse.peek_eq hs₅)]
  have hb' : (u.kind == .keyword "else") = false := by simp [hu]
  simp only [Token.isKeyword, hb', Bool.false_eq_true, ↓reduceIte, Parse.pure_bind]
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl

/-- `if ( test )`, a branch, `else` and a branch, which `parseBranch` reads. -/
theorem stmt_if_some {T : Edition} {fn loop : Bool} (g : Nat) (sp : Span) (test : Expr) (t e : Stmt)
    (hw : (Stmt.ifStmt sp test t (some e)).wf T fn loop = true)
    (ht : ReadsS T fn loop (Parse.parseBranch (g + 1)) t)
    (he : ReadsS T fn loop (Parse.parseBranch (g + 1)) e) :
    ReadsS T fn loop (Parse.parseStatement (g + 1 + 1)) (.ifStmt sp test t (some e)) := by
  intro s ts rest hT hF hL hs hl hlaid hr hopen
  simp only [Stmt.wf, Bool.and_eq_true, Expr.wfParen, Bool.not_eq_true'] at hw
  obtain ⟨⟨⟨⟨⟨⟨hwe, hae⟩, -⟩, -⟩, hto⟩, -⟩, -⟩ := hw
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons, List.map_append] at hlaid
  rw [Stmt.lines_words t 1, Stmt.lines_words e 1] at hlaid
  obtain ⟨a, b, rfl, ha, hna, _, hb⟩ := Laid.cons hlaid
  obtain ⟨k, lp, tts, rp, rfl, hk, hlp, htt, hrp⟩ := Touching.keywordParen ha
  obtain ⟨b₁, b₂, rfl, hb₁, hb₂, _⟩ := Laid.append hb
  obtain ⟨el, b₃, rfl, hel, _, _, hb₃⟩ := Laid.cons hb₂
  obtain ⟨ek, el', rfl, hek, h'⟩ := Touching.cons_one (by simpa [keywordWord] using hel)
  simp [Touching] at h'; subst h'
  have hs' : s.rest = k :: lp :: (tts ++ rp :: (b₁ ++ ek :: (b₃ ++ rest))) := by simpa using hs
  let s₁ := past s k (lp :: (tts ++ rp :: (b₁ ++ ek :: (b₃ ++ rest))))
  let s₂ : ParseState := { s₁ with rest := tts ++ rp :: (b₁ ++ ek :: (b₃ ++ rest)), left := s₁.left - 1, lastStop := lp.span.stop }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁, hl, hs']
  obtain ⟨test', s₃, hpt, het, hL₃⟩ := parseExpression_budget test hwe s₂ tts (rp :: (b₁ ++ ek :: (b₃ ++ rest)))
    hT rfl hl₂ htt (fun y hy => hna y (by simp [List.mem_of_mem_tail hy])) (by simp) (EndsExpr.closer hrp)
    (by simpa [hrp] using afterOK_closer hae _)
  have hs₃ : s₃.rest = rp :: (b₁ ++ ek :: (b₃ ++ rest)) := hL₃.rest_eq
  let s₄ : ParseState := { s₃ with rest := b₁ ++ ek :: (b₃ ++ rest), left := s₃.left - 1, lastStop := rp.span.stop }
  have hl₄ : s₄.left = s₄.rest.length := by simp [s₄, hL₃.left_eq]
  obtain ⟨t', s₅, hpb, het', hL₅⟩ := ht s₄ b₁ (ek :: (b₃ ++ rest)) (hL₃.target_eq.trans hT)
    (hL₃.inFunction_eq.trans hF) (fun h => by simp only [s₄]; rw [hL₃.loopDepth_eq]; exact hL h) rfl hl₄ hb₁
    (by simp) (fun h => by rw [hto] at h; cases h)
  have hs₅ : s₅.rest = ek :: (b₃ ++ rest) := hL₅.rest_eq
  let s₆ : ParseState := { s₅ with rest := b₃ ++ rest, left := s₅.left - 1, lastStop := ek.span.stop }
  have hl₆ : s₆.left = s₆.rest.length := by simp [s₆, hL₅.left_eq]
  obtain ⟨e', s₇, hpe, hee, hL₇⟩ := he s₆ b₃ rest (hL₅.target_eq.trans (hL₃.target_eq.trans hT))
    (hL₅.inFunction_eq.trans (hL₃.inFunction_eq.trans hF))
    (fun h => by simp only [s₆]; rw [hL₅.loopDepth_eq, hL₃.loopDepth_eq]; exact hL h) rfl hl₆ hb₃ hr
    (fun h => hopen h)
  refine ⟨.ifStmt ⟨k.span.start, s₇.lastStop⟩ test' t' (some e'), s₇, ?_,
    by simp [Stmt.erase, Stmt.eraseOpt, het, het', hee],
    leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans hL₃ (leaves_trans (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃])) (leaves_trans hL₅
        (leaves_trans (leaves_advance hs₅ (by rw [hL₅.left_eq, hs₅])) hL₇)))))⟩
  simp only [Parse.parseStatement]
  rw [Parse.bind_eq (Parse.peek_eq hs')]
  simp only [hk]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')),
    Parse.bind_eq (Parse.expectPunct_ok (s := s₁) rfl (by simp) hlp), Parse.bind_eq (Parse.budget_eq _),
    Parse.bind_eq hpt, Parse.bind_eq (Parse.expectPunct_ok hs₃ (by simp) hrp), Parse.bind_eq hpb,
    Parse.bind_eq (Parse.peek_eq hs₅)]
  simp only [Token.isKeyword, hek, beq_self_eq_true, ↓reduceIte]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs₅ (by simp [hr]))), Parse.bind_eq hpe,
    Parse.pure_bind, Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl


theorem Parse.withLoop_ok {α : Type} {body : ParseM α} {s s' : ParseState} {a : α}
    (h : body { s with loopDepth := s.loopDepth + 1 } = .ok a s') :
    Parse.withLoop body s = .ok a { s' with loopDepth := s'.loopDepth - 1 } := by
  simp [Parse.withLoop, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, bind, EStateM.bind, h,
    pure, EStateM.pure]

theorem leaves_withLoop {s s' : ParseState} {r : List Token}
    (h : Leaves { s with loopDepth := s.loopDepth + 1 } s' r) :
    Leaves s { s' with loopDepth := s'.loopDepth - 1 } r where
  rest_eq := h.rest_eq
  left_eq := h.left_eq
  eof_eq := h.eof_eq
  inFunction_eq := h.inFunction_eq
  loopDepth_eq := by simp [h.loopDepth_eq]
  target_eq := h.target_eq

/-- `while ( test )` and a body, which `parseBranch` reads in a loop. -/
theorem stmt_while {T : Edition} {fn loop : Bool} (g : Nat) (sp : Span) (test : Expr) (body : Stmt)
    (hw : (Stmt.whileStmt sp test body).wf T fn loop = true)
    (hb : ReadsS T fn true (Parse.parseBranch (g + 1)) body) :
    ReadsS T fn loop (Parse.parseStatement (g + 1 + 1)) (.whileStmt sp test body) := by
  intro s ts rest hT hF _ hs hl hlaid hr hopen
  simp only [Stmt.wf, Bool.and_eq_true, Expr.wfParen] at hw
  obtain ⟨⟨⟨hwe, hae⟩, -⟩, -⟩ := hw
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons] at hlaid
  rw [Stmt.lines_words body 1] at hlaid
  obtain ⟨a, b, rfl, ha, hna, _, hbl⟩ := Laid.cons hlaid
  obtain ⟨k, lp, tts, rp, rfl, hk, hlp, htt, hrp⟩ := Touching.keywordParen ha
  have hs' : s.rest = k :: lp :: (tts ++ rp :: (b ++ rest)) := by simpa using hs
  let s₁ := past s k (lp :: (tts ++ rp :: (b ++ rest)))
  let s₂ : ParseState := { s₁ with rest := tts ++ rp :: (b ++ rest), left := s₁.left - 1, lastStop := lp.span.stop }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁, hl, hs']
  obtain ⟨test', s₃, hpt, het, hL₃⟩ := parseExpression_budget test hwe s₂ tts (rp :: (b ++ rest)) hT rfl hl₂ htt
    (fun y hy => hna y (by simp [List.mem_of_mem_tail hy])) (by simp) (EndsExpr.closer hrp)
    (by simpa [hrp] using afterOK_closer hae _)
  have hs₃ : s₃.rest = rp :: (b ++ rest) := hL₃.rest_eq
  let s₄ : ParseState := { s₃ with rest := b ++ rest, left := s₃.left - 1, lastStop := rp.span.stop }
  let s₄' : ParseState := { s₄ with loopDepth := s₄.loopDepth + 1 }
  have hl₄ : s₄'.left = s₄'.rest.length := by simp [s₄', s₄, hL₃.left_eq]
  obtain ⟨body', s₅, hpb, heb, hL₅⟩ := hb s₄' b rest (hL₃.target_eq.trans hT) (hL₃.inFunction_eq.trans hF)
    (fun _ => by simp [s₄']) rfl hl₄ hbl hr (fun h => hopen h)
  refine ⟨.whileStmt ⟨k.span.start, s₅.lastStop⟩ test' body', { s₅ with loopDepth := s₅.loopDepth - 1 }, ?_,
    by simp [Stmt.erase, het, heb],
    leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans hL₃ (leaves_trans (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃])) (leaves_withLoop hL₅))))⟩
  simp only [Parse.parseStatement]
  rw [Parse.bind_eq (Parse.peek_eq hs')]
  simp only [hk]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')),
    Parse.bind_eq (Parse.expectPunct_ok (s := s₁) rfl (by simp) hlp), Parse.bind_eq (Parse.budget_eq _),
    Parse.bind_eq hpt, Parse.bind_eq (Parse.expectPunct_ok hs₃ (by simp [hr]) hrp),
    Parse.bind_eq (Parse.withLoop_ok hpb), Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl


/-- `for ( const x of e )` or `for ( let x of e )`, and a body, which `parseBranch` reads in a loop. -/
theorem parseForOf_reads {T : Edition} {fn loop : Bool} (h : Nat) (sp : Span) (kind : VarKind) (name : String)
    (it : Expr) (body : Stmt) (hw : (Stmt.forOfStmt sp kind name it body).wf T fn loop = true)
    (hb : ReadsS T fn true (Parse.parseBranch h) body) :
    ReadsS T fn loop (Parse.parseForOf (h + 1)) (.forOfStmt sp kind name it body) := by
  intro s ts rest hT hF _ hs hl hlaid hr hopen
  simp only [Stmt.wf, Bool.and_eq_true, Expr.wfParen] at hw
  obtain ⟨⟨⟨hname, hwe, hae⟩, -⟩, -⟩ := hw
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons] at hlaid
  rw [Stmt.lines_words body 1] at hlaid
  obtain ⟨a, b, rfl, ha, hna, _, hbl⟩ := Laid.cons hlaid
  simp only [VarKind.word_eq] at ha
  obtain ⟨fk, a₁, rfl, hfk, h₁⟩ := Touching.cons_one (by simpa [keywordWord] using ha)
  obtain ⟨lp, a₂, rfl, hlp, h₂⟩ := Touching.cons_one (by simpa [punctWord] using h₁)
  obtain ⟨kk, a₃, rfl, hkk, h₃⟩ := Touching.cons_one h₂
  obtain ⟨nm, a₄, rfl, hnm, h₄⟩ := Touching.cons_one (by simpa [identWord] using h₃)
  obtain ⟨ofk, a₅, rfl, hofk, h₅⟩ := Touching.cons_one (by simpa [identWord] using h₄)
  obtain ⟨its, a₆, rfl, hit, h₆⟩ := Touching.append_split h₅
  obtain ⟨rp, a₇, rfl, hrp, h₇⟩ := Touching.cons_one (by simpa [punctWord] using h₆)
  simp [Touching] at h₇; subst h₇
  have hs' : s.rest = fk :: lp :: kk :: nm :: ofk :: (its ++ rp :: (b ++ rest)) := by simpa using hs
  let s₁ := past s fk (lp :: (kk :: nm :: ofk :: (its ++ rp :: (b ++ rest))))
  let s₂ := past s₁ lp (kk :: (nm :: ofk :: (its ++ rp :: (b ++ rest))))
  let s₃ := past s₂ kk (nm :: (ofk :: (its ++ rp :: (b ++ rest))))
  let s₄ := past s₃ nm (ofk :: (its ++ rp :: (b ++ rest)))
  let s₅ : ParseState := { s₄ with rest := its ++ rp :: (b ++ rest), left := s₄.left - 1, lastStop := ofk.span.stop }
  have hl₅ : s₅.left = s₅.rest.length := by simp [s₅, s₄, s₃, s₂, s₁, hl, hs']
  obtain ⟨it', s₆, hpi, hei, hL₆⟩ := parseAssign_budget it hwe s₅ its (rp :: (b ++ rest)) hT rfl hl₅ hit
    (fun y hy => hna y (by simp [List.mem_of_mem_tail hy])) (by simp)
    (endsAssign_separator hrp (by simp [separators])) (by simpa [hrp] using afterOK_closer hae _)
  have hs₆ : s₆.rest = rp :: (b ++ rest) := hL₆.rest_eq
  let s₇ : ParseState := { s₆ with rest := b ++ rest, left := s₆.left - 1, lastStop := rp.span.stop }
  let s₇' : ParseState := { s₇ with loopDepth := s₇.loopDepth + 1 }
  have hl₇ : s₇'.left = s₇'.rest.length := by simp [s₇', s₇, hL₆.left_eq]
  obtain ⟨body', s₈, hpb, heb, hL₈⟩ := hb s₇' b rest (hL₆.target_eq.trans hT) (hL₆.inFunction_eq.trans hF)
    (fun _ => by simp [s₇']) rfl hl₇ hbl hr (fun h => hopen h)
  have hnot : nm.kind ≠ .punct "[" ∧ nm.kind ≠ .punct "{" := by rw [hnm]; simp
  have hlp' : lp.kind ≠ .ident "await" := by rw [hlp]; simp
  refine ⟨.forOfStmt ⟨fk.span.start, s₈.lastStop⟩ kind name it' body', { s₈ with loopDepth := s₈.loopDepth - 1 },
    ?_, by simp [Stmt.erase, hei, heb], ?_⟩
  · simp only [Parse.parseForOf]
    rw [Parse.bind_eq (Parse.advance_eq hs'), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
    rw [Parse.ite_guard (fun h => by simp [Token.isIdent, hlp'] at h)]
    rw [Parse.bind_eq (Parse.expectPunct_ok (s := s₁) rfl (by simp) hlp), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    cases kind <;> simp only [VarKind.token] at hkk <;>
    simp (config := { decide := true }) only [Token.isPunct, Token.isKeyword, Token.isIdent, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
      Parse.pure_bind, reduceCtorEq, hkk] <;>
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₂) rfl)), Parse.bind_eq (Parse.peek_eq (s := s₃) rfl)] <;>
    rw [Parse.ite_guard (fun h => by simp [hnot] at h)] <;>
    rw [Parse.bind_eq (readName_ok (s := s₃) rfl hnm hname'), Parse.bind_eq (Parse.peek_eq (s := s₄) rfl)] <;>
    simp (config := { decide := true }) only [beq_self_eq_true, ↓reduceIte,
      Parse.pure_bind, hofk] <;>
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₄) rfl (by simp))), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_eq hpi, Parse.bind_eq (Parse.expectPunct_ok hs₆ (by simp [hr]) hrp),
      Parse.bind_eq (Parse.withLoop_ok hpb), Parse.bind_eq (Parse.spanFrom_eq _ _)] <;> rfl
  · exact leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs']))
        (leaves_trans (leaves_advance (s := s₃) rfl (by simp [s₃, s₂, s₁, hl, hs']))
          (leaves_trans (leaves_advance (s := s₄) rfl (by simp [s₄, s₃, s₂, s₁, hl, hs']))
            (leaves_trans hL₆ (leaves_trans (leaves_advance hs₆ (by rw [hL₆.left_eq, hs₆])) (leaves_withLoop hL₈)))))))

/-- `parseStatement` reads `for … of` with `parseForOf`. -/
theorem stmt_for {T : Edition} {fn loop : Bool} (f : Nat) (st : Stmt)
    (hst : ∃ sp kind name it body, st = .forOfStmt sp kind name it body)
    (h : ReadsS T fn loop (Parse.parseForOf f) st) :
    ReadsS T fn loop (Parse.parseStatement (f + 1)) st := by
  intro s ts rest hT hF hL hs hl ht hr he
  obtain ⟨sp, kind, name, it, body, rfl⟩ := hst
  obtain ⟨st', s', hp, hst', hL'⟩ := h s ts rest hT hF hL hs hl ht hr he
  refine ⟨st', s', ?_, hst', hL'⟩
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons] at ht
  obtain ⟨a, b, rfl, ha, _⟩ := Laid.cons ht
  obtain ⟨fk, a', rfl, hfk, _⟩ := Touching.cons_one (by simpa [keywordWord] using ha)
  simp only [Parse.parseStatement]
  rw [Parse.bind_eq (Parse.peek_eq (by simpa using hs))]
  simp only [hfk]
  exact hp


/-! ### Every statement -/

/-- The fuel that `parseStatement` needs to read `st`. -/
def Stmt.need (st : Stmt) : Nat := 3 * st.depth + 2

/-- `parseStatement`, with fuel `f`, reads every well-formed statement that needs
at most `f`. -/
def AllStmts (T : Edition) (f : Nat) : Prop :=
  ∀ (fn loop : Bool) (st : Stmt), st.wf T fn loop = true → st.need ≤ f →
    ReadsS T fn loop (Parse.parseStatement f) st

theorem Stmt.allWF_iff {T : Edition} {fn loop : Bool} :
    ∀ {ss : List Stmt}, Stmt.allWF T fn loop ss = true ↔ ∀ st ∈ ss, st.wf T fn loop = true
  | [] => by simp [Stmt.allWF]
  | st :: ss => by simp [Stmt.allWF, Stmt.allWF_iff]

theorem Stmt.depth_le_depthOf {st : Stmt} : ∀ {ss : List Stmt}, st ∈ ss → st.depth ≤ Stmt.depthOf ss
  | s :: ss, h => by
    simp at h
    rcases h with rfl | h
    · simp [Stmt.depthOf]; omega
    · have := Stmt.depth_le_depthOf h; simp [Stmt.depthOf]; omega

theorem allStmts_succ {T : Edition} (f : Nat) (IH : ∀ g ≤ f, AllStmts T g) : AllStmts T (f + 1) := by
  intro fn loop st hw hn
  simp only [Stmt.need] at hn
  cases st with
  | varDecl sp d => exact stmt_varDecl f sp d hw
  | exprStmt sp e =>
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [Stmt.depth] at hn; omega⟩
    exact stmt_expr g sp e hw
  | returnStmt sp v =>
    cases v with
    | none =>
      simp only [Stmt.wf] at hw; subst hw; exact stmt_return_none f sp
    | some e =>
      simp only [Stmt.wf, Bool.and_eq_true] at hw
      obtain ⟨⟨hfn, he⟩, ha⟩ := hw
      subst hfn; exact stmt_return_some f sp e he ha
  | ifStmt sp test t e =>
    cases e with
    | none =>
      simp only [Stmt.depth] at hn
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      have hw' := hw
      simp only [Stmt.wf, Bool.and_eq_true, Bool.not_eq_true'] at hw'
      obtain ⟨⟨_, hd⟩, htw⟩ := hw'
      exact stmt_if_none g sp test t hw (parseBranch_reads g t hd htw
        (IH g (by omega) fn loop t htw (by simp [Stmt.need]; omega)))
    | some e =>
      simp only [Stmt.depth] at hn
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      have hw' := hw
      simp only [Stmt.wf, Bool.and_eq_true, Bool.not_eq_true'] at hw'
      obtain ⟨⟨⟨⟨⟨_, hd⟩, htw⟩, _⟩, hde⟩, hew⟩ := hw'
      exact stmt_if_some g sp test t e hw
        (parseBranch_reads g t hd htw (IH g (by omega) fn loop t htw (by simp [Stmt.need]; omega)))
        (parseBranch_reads g e hde hew (IH g (by omega) fn loop e hew (by simp [Stmt.need]; omega)))
  | forOfStmt sp kind name it body =>
    simp only [Stmt.depth] at hn
    obtain ⟨h, rfl⟩ : ∃ h, f = h + 1 + 1 := ⟨f - 2, by omega⟩
    have hw' := hw
    simp only [Stmt.wf, Bool.and_eq_true, Bool.not_eq_true'] at hw'
    obtain ⟨⟨_, hd⟩, hbw⟩ := hw'
    exact stmt_for (h + 1 + 1) _ ⟨sp, kind, name, it, body, rfl⟩
      (parseForOf_reads (h + 1) sp kind name it body hw
        (parseBranch_reads h body hd hbw (IH h (by omega) fn true body hbw (by simp [Stmt.need]; omega))))
  | whileStmt sp test body =>
    simp only [Stmt.depth] at hn
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hw' := hw
    simp only [Stmt.wf, Bool.and_eq_true, Bool.not_eq_true'] at hw'
    obtain ⟨⟨_, hd⟩, hbw⟩ := hw'
    exact stmt_while g sp test body hw
      (parseBranch_reads g body hd hbw (IH g (by omega) fn true body hbw (by simp [Stmt.need]; omega)))
  | block sp body =>
    simp only [Stmt.depth] at hn
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [Stmt.wf] at hw
    exact stmt_block (g + 1) sp body (parseBlock_reads g sp body fun st hst =>
      ⟨Stmt.allWF_iff.mp hw st hst, IH g (by omega) fn loop st (Stmt.allWF_iff.mp hw st hst)
        (by have := Stmt.depth_le_depthOf hst; simp [Stmt.need]; omega)⟩)
  | breakStmt sp =>
    simp only [Stmt.wf] at hw; subst hw
    exact stmt_jump f _ "break" ⟨rfl, .inl rfl⟩ fun sp' => by simp [Stmt.erase]
  | continueStmt sp =>
    simp only [Stmt.wf] at hw; subst hw
    exact stmt_jump f _ "continue" ⟨rfl, .inr rfl⟩ fun sp' => by simp [Stmt.erase]
  | empty sp => exact stmt_empty f sp

theorem stmts_read_le (T : Edition) : ∀ f, ∀ g ≤ f, AllStmts T g := by
  intro f
  induction f with
  | zero =>
    intro g hg fn loop st _ hn
    simp [Stmt.need] at hn; omega
  | succ f ih =>
    intro g hg
    by_cases h : g ≤ f
    · exact ih g h
    · have : g = f + 1 := by omega
      subst this
      exact allStmts_succ f ih

/-- The parser's round trip for statements, on tokens: with fuel `f`,
`parseStatement` reads the printed tokens of every well-formed statement that
needs at most `f`, as that statement apart from spans. -/
theorem stmts_read (T : Edition) (f : Nat) : AllStmts T f := stmts_read_le T f f (Nat.le_refl _)

end tolean.TypeScript.Syntax
