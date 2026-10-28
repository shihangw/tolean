import tolean.TypeScript.Syntax.RoundTripStmt

/-!
The parser's round trip for declarations and modules, on tokens: the parser
reads the tokens that `Syntax/Source.lean` prints for a declaration as the
same declaration, apart from spans.

A declaration parses its parts with the fuel that `budget` gives. A statement
nests no deeper than it has tokens (`Stmt.depth_lt`), so that fuel is enough
for a statement or a block (`parseStatement_budget`, `parseBlock_budget`).
-/
namespace tolean.TypeScript.Syntax

open tolean

set_option linter.unusedSimpArgs false

/-! ### Parameters -/

/-- What `Decl.erase` does to a parameter. -/
def Param.erase (p : Param) : Param := { p with span := noSpan, type := p.type.map TypeExpr.erase }

def Param.wf (p : Param) : Bool := exprName p.name && (match p.type with | some t => t.wf | none => true)

/-- A parameter's type ends before `,` or `)`. -/
theorem followsType_item {u : Token} {r : List Token} (hu : u.kind = .punct "," ∨ u.kind = .punct ")") :
    FollowsType (u :: r) := by
  rcases hu with hu | hu <;> exact followsType_punct hu (by simp)

theorem parseParam_reads {T : Edition} (p : Param) (hp : p.wf = true) :
    ReadsW T Param.erase Param.words (fun _ _ => true) Parse.parseParam p (EndsItem ")") := by
  intro s ts rest _ hs hl ht hn hr hE _
  obtain ⟨sp, name, type⟩ := p
  simp only [Param.wf, Bool.and_eq_true] at hp
  obtain ⟨hname, hty⟩ := hp
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  obtain ⟨u, r, rfl, hu⟩ := hE
  have hu1 : u.kind ≠ .punct "?" := by rcases hu with h | h <;> rw [h] <;> exact punct_ne (by decide)
  have hu2 : u.kind ≠ .punct "=" := by rcases hu with h | h <;> rw [h] <;> exact punct_ne (by decide)
  have hu3 : u.kind ≠ .punct ":" := by rcases hu with h | h <;> rw [h] <;> exact punct_ne (by decide)
  simp only [Param.words] at ht
  obtain ⟨nm, ts', rfl, hnm, h'⟩ := Touching.cons_one (by simpa [identWord] using ht)
  have hn1 : nm.kind ≠ .punct "..." ∧ nm.kind ≠ .punct "[" ∧ nm.kind ≠ .punct "{" ∧ nm.kind ≠ .keyword "this" := by
    rw [hnm]; simp
  cases type with
  | none =>
    simp [Touching] at h'; subst h'
    have hs' : s.rest = nm :: u :: r := by simpa using hs
    let s₁ := advanced s nm u r
    refine ⟨⟨⟨nm.span.start, nm.span.stop⟩, name, none⟩, s₁, ?_, rfl, leaves_advanced hs' hl⟩
    simp only [Parse.parseParam]
    rw [Parse.bind_eq (Parse.peek_eq hs')]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hn1] at h),
      Parse.ite_guard (fun h => by simp [Token.isPunct, hn1] at h),
      Parse.ite_guard (fun h => by simp [Token.isKeyword, hn1] at h)]
    rw [Parse.bind_eq (readName_ok hs' hnm hname'), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hu1] at h)]
    rw [if_neg (by simp [Token.isPunct, hu3]), Parse.pure_bind, Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hu2] at h)]
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  | some t =>
    obtain ⟨colon, ts₂, rfl, hcolon, h₂⟩ := Touching.cons_one (by simpa [punctWord] using h')
    have hs' : s.rest = nm :: colon :: (ts₂ ++ u :: r) := by simpa using hs
    let s₁ := advanced s nm colon (ts₂ ++ u :: r)
    let s₂ : ParseState := { s₁ with rest := ts₂ ++ u :: r, left := s₁.left - 1, lastStop := colon.span.stop }
    have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁, hl, hs']
    obtain ⟨t', s₃, hpt, het, hL₃⟩ := parseType_budget t (by simpa using hty) s₂ ts₂ (u :: r) rfl hl₂ h₂.kinds
      (fun y hy => hn y (by simp [hy])) (by simp) (followsType_item hu)
    have hs₃ : s₃.rest = u :: r := hL₃.rest_eq
    have hc1 : colon.kind ≠ .punct "?" := by rw [hcolon]; exact punct_ne (by decide)
    refine ⟨⟨⟨nm.span.start, s₃.lastStop⟩, name, some t'⟩, s₃, ?_, by simp [Param.erase, het],
      leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs'])) hL₃)⟩
    simp only [Parse.parseParam]
    rw [Parse.bind_eq (Parse.peek_eq hs')]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hn1] at h),
      Parse.ite_guard (fun h => by simp [Token.isPunct, hn1] at h),
      Parse.ite_guard (fun h => by simp [Token.isKeyword, hn1] at h)]
    rw [Parse.bind_eq (readName_ok hs' hnm hname'), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hc1] at h)]
    rw [if_pos (by simp [Token.isPunct, hcolon])]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₁) rfl (by simp))),
      Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpt, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₃)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hu2] at h)]
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl


/-! ### Fuel for a statement -/

/-- The tokens of a statement's lines. -/
def Stmt.tokens (st : Stmt) : List TokenKind := st.wordLines.flatten.flatten

theorem Stmt.wordLines_if_none (sp : Span) (test : Expr) (t : Stmt) :
    (Stmt.ifStmt sp test t none).wordLines =
      (keywordWord "if" :: punctWord "(" :: test.words ++ [punctWord ")"]) :: t.wordLines := by
  simp [Stmt.wordLines, Stmt.lines, Stmt.lines_words t 1]

theorem Stmt.wordLines_if_some (sp : Span) (test : Expr) (t e : Stmt) :
    (Stmt.ifStmt sp test t (some e)).wordLines =
      (keywordWord "if" :: punctWord "(" :: test.words ++ [punctWord ")"]) :: (t.wordLines ++
        [keywordWord "else"] :: e.wordLines) := by
  simp [Stmt.wordLines, Stmt.lines, Stmt.lines_words t 1, Stmt.lines_words e 1]

theorem Stmt.tokens_length_cons {st : Stmt} {l : List Word} {ls : List (List Word)} (h : st.wordLines = l :: ls) :
    st.tokens.length = l.flatten.length + (ls.flatten.flatten).length := by
  simp only [Stmt.tokens, h, List.flatten_cons, List.flatten_append, List.length_append]

theorem Stmt.tokensOf (ss : List Stmt) :
    (ss.map Stmt.wordLines).flatten.flatten.flatten = (ss.map Stmt.tokens).flatten := by
  induction ss with
  | nil => rfl
  | cons st ss ih => simp only [List.map_cons, List.flatten_cons, List.flatten_append, ih]; rfl

theorem Stmt.tokens_eq (st : Stmt) : st.wordLines.flatten.flatten = st.tokens := rfl

mutual

/-- A statement nests no deeper than it has tokens. -/
theorem Stmt.depth_lt : ∀ st : Stmt, st.depth < st.tokens.length
  | .ifStmt sp test t none => by
    have := Stmt.depth_lt t
    rw [Stmt.tokens_length_cons (Stmt.wordLines_if_none sp test t), Stmt.tokens_eq]
    simp only [Stmt.depth]
    have : 1 ≤ (keywordWord "if" :: punctWord "(" :: test.words ++ [punctWord ")"]).flatten.length := by
      simp [keywordWord]
    omega
  | .ifStmt sp test t (some e) => by
    have := Stmt.depth_lt t; have := Stmt.depth_lt e
    rw [Stmt.tokens_length_cons (Stmt.wordLines_if_some sp test t e)]
    simp only [List.flatten_append, List.flatten_cons, List.length_append, Stmt.tokens_eq, Stmt.depth]
    have : 1 ≤ (keywordWord "if" :: punctWord "(" :: test.words ++ [punctWord ")"]).flatten.length := by
      simp [keywordWord]
    omega
  | .forOfStmt sp k n it b => by
    have := Stmt.depth_lt b
    rw [Stmt.tokens_length_cons (l := keywordWord "for" :: punctWord "(" :: k.word :: identWord n :: identWord "of" ::
      it.words ++ [punctWord ")"]) (ls := b.wordLines)
      (by simp [Stmt.wordLines, Stmt.lines, Stmt.lines_words b 1]), Stmt.tokens_eq]
    simp only [Stmt.depth]
    have : 1 ≤ (keywordWord "for" :: punctWord "(" :: k.word :: identWord n :: identWord "of" ::
      it.words ++ [punctWord ")"]).flatten.length := by simp [keywordWord]
    omega
  | .whileStmt sp test b => by
    have := Stmt.depth_lt b
    rw [Stmt.tokens_length_cons (l := keywordWord "while" :: punctWord "(" :: test.words ++ [punctWord ")"])
      (ls := b.wordLines) (by simp [Stmt.wordLines, Stmt.lines, Stmt.lines_words b 1]), Stmt.tokens_eq]
    simp only [Stmt.depth]
    have : 1 ≤ (keywordWord "while" :: punctWord "(" :: test.words ++ [punctWord ")"]).flatten.length := by
      simp [keywordWord]
    omega
  | .block sp body => by
    have := Stmt.depthOf_le body
    rw [Stmt.tokens_length_cons (l := [punctWord "{"]) (ls := (body.map Stmt.wordLines).flatten ++ [[punctWord "}"]])
      (by simp [Stmt.wordLines, Stmt.lines, Stmt.linesOf_wordLines])]
    simp only [Stmt.depth, List.flatten_append, List.length_append, Stmt.tokensOf, punctWord, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.length_cons, List.length_nil]
    omega
  | .varDecl _ d => by
    simp [Stmt.depth, Stmt.tokens, Stmt.wordLines, Stmt.lines, VarDecl.words, VarKind.word_eq]
  | .exprStmt _ e => by simp [Stmt.depth, Stmt.tokens, Stmt.wordLines, Stmt.lines, punctWord]
  | .returnStmt _ v => by cases v <;> simp [Stmt.depth, Stmt.tokens, Stmt.wordLines, Stmt.lines, keywordWord]
  | .breakStmt _ | .continueStmt _ => by simp [Stmt.depth, Stmt.tokens, Stmt.wordLines, Stmt.lines, keywordWord]
  | .empty _ => by simp [Stmt.depth, Stmt.tokens, Stmt.wordLines, Stmt.lines, punctWord]

theorem Stmt.depthOf_le : ∀ ss : List Stmt, Stmt.depthOf ss ≤ (ss.map Stmt.tokens).flatten.length
  | [] => by simp [Stmt.depthOf]
  | st :: ss => by
    have := Stmt.depth_lt st; have := Stmt.depthOf_le ss
    simp only [Stmt.depthOf, List.map_cons, List.flatten_cons, List.length_append]
    omega

end


/-- `need` fits in the fuel that `budget` gives for a statement's tokens and what follows them. -/
theorem Stmt.need_le_budget {st : Stmt} {s : ParseState} {ts rest : List Token}
    (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length) (ht : Laid ts st.wordLines) :
    st.need + 1 ≤ 10 * (s.left + 1) := by
  have h1 := Stmt.depth_lt st
  have h2 : ts.length = st.tokens.length := by
    have := congrArg List.length ht.kinds; simpa [Stmt.tokens] using this
  have h3 : ts.length ≤ s.left := by rw [hl, hs, List.length_append]; omega
  simp only [Stmt.need]; omega

/-- `parseStatement`, with the fuel that `budget` gives, reads every well-formed statement. -/
theorem parseStatement_budget {T : Edition} {fn loop : Bool} (st : Stmt) (hw : st.wf T fn loop = true) :
    ∀ (s : ParseState) (ts rest : List Token), s.target = T → s.inFunction = fn →
      (loop = true → s.loopDepth ≠ 0) → s.rest = ts ++ rest → s.left = s.rest.length →
      Laid ts st.wordLines → rest ≠ [] → (st.openIf = true → ∀ u ∈ rest.head?, u.kind ≠ .keyword "else") →
      ∃ st' s', Parse.parseStatement (10 * (s.left + 1)) s = .ok st' s' ∧ st'.erase = st.erase ∧
        Leaves s s' rest :=
  fun s ts rest hT hF hL hs hl ht hr he =>
    stmts_read T _ fn loop st hw (by have := Stmt.need_le_budget hs hl ht; omega) s ts rest hT hF hL hs hl ht hr he

/-- `parseBlock`, with the fuel that `budget` gives, reads every well-formed block. -/
theorem parseBlock_budget {T : Edition} {fn loop : Bool} (sp : Span) (body : List Stmt)
    (hw : (Stmt.block sp body).wf T fn loop = true) :
    ∀ (s : ParseState) (ts rest : List Token), s.target = T → s.inFunction = fn →
      (loop = true → s.loopDepth ≠ 0) → s.rest = ts ++ rest → s.left = s.rest.length →
      Laid ts (Stmt.block sp body).wordLines → rest ≠ [] →
      ∃ st' s', Parse.parseBlock (10 * (s.left + 1)) s = .ok st' s' ∧ st'.erase = (Stmt.block sp body).erase ∧
        Leaves s s' rest := by
  intro s ts rest hT hF hL hs hl ht hr
  have hb := Stmt.need_le_budget hs hl ht
  have hd := Stmt.depthOf_le body
  have hlt := Stmt.depth_lt (.block sp body)
  simp only [Stmt.need, Stmt.depth] at hb hlt
  obtain ⟨g, hg⟩ : ∃ g, 10 * (s.left + 1) = g + 1 := ⟨10 * s.left + 9, by omega⟩
  rw [hg]
  simp only [Stmt.wf] at hw
  exact parseBlock_reads g sp body (fun st hst => ⟨Stmt.allWF_iff.mp hw st hst,
    stmts_read T g fn loop st (Stmt.allWF_iff.mp hw st hst)
      (by have := Stmt.depth_le_depthOf hst; simp only [Stmt.need]; omega)⟩)
    s ts rest hT hF hL hs hl ht hr (fun h => by simp [Stmt.openIf] at h)

/-! ### Functions -/

theorem Parse.modify_eq (f : ParseState → ParseState) (s : ParseState) :
    (modify f : ParseM PUnit) s = .ok () (f s) := rfl

theorem leaves_inFunction {s s' : ParseState} {r : List Token} (hs : s.inFunction = false)
    (h : Leaves { s with inFunction := true } s' r) : Leaves s { s' with inFunction := false } r where
  rest_eq := h.rest_eq
  left_eq := h.left_eq
  eof_eq := h.eof_eq
  inFunction_eq := hs.symm
  loopDepth_eq := h.loopDepth_eq
  target_eq := h.target_eq

theorem listAfter_true {α : Type} {tokens : α → List TokenKind} {close : List TokenKind} :
    ∀ xs : List α, ListAfter (fun _ _ => true) tokens close xs
  | [] => trivial
  | [_] => rfl
  | _ :: y :: xs => ⟨rfl, listAfter_true (y :: xs)⟩

/-- The words of a return type. -/
def rtWords : Option TypeExpr → List Word
  | some t => punctWord ":" :: t.words
  | none => []

theorem rtWords_eq (rt : Option TypeExpr) :
    (match rt with | some t => punctWord ":" :: t.words | none => []) = rtWords rt := by
  cases rt <;> rfl

/-- `( params )`, which `listStep` and `parseParam` read. -/
theorem params_reads {T : Edition} (params : List Param) (hps : ∀ p ∈ params, p.wf = true)
    (s : ParseState) (its rest : List Token) (rp : Token) (hT : s.target = T) (hs : s.rest = its ++ rp :: rest)
    (hrp : rp.kind = .punct ")") (hl : s.left = s.rest.length)
    (ht : Touching its (commas (params.map Param.words))) (hn : ∀ y ∈ its, y.newlineBefore = false) :
    ∃ res s', Parse.iterate (10 * (s.left + 1)) #[] (Parse.listStep ")" (fun _ => pure ()) Parse.parseParam) s =
      .ok res s' ∧ res.toList.map Param.erase = params.map Param.erase ∧ Leaves s s' (rp :: rest) := by
  obtain ⟨res, s', hit, he, hL⟩ := iterate_list (close := ")") (refuse := fun _ => pure ()) (by decide)
    params (10 * (s.left + 1)) #[] s its rest rp (fun p hp => parseParam_reads p (hps p hp))
    (fun p _ => ⟨.ident p.name, by simp [Param.words, identWord], by simp, fun _ _ _ => rfl⟩)
    (by have := length_items ht; have : s.left = its.length + rest.length + 1 := by simp [hl, hs]; omega
        omega) hT hs hrp hl ht hn (listAfter_true params)
  exact ⟨res, s', hit, by simpa using he, hL⟩


/-- `function`, a name, `( params )`, a return type or none, and a block, which
`parseBlock` reads in a function. -/
theorem parseFunction_reads {T : Edition} (start : Pos) (exported : Bool) (sp : Span) (name : String)
    (params : List Param) (rt : Option TypeExpr) (bsp : Span) (bs : List Stmt)
    (hname : exprName name = true) (hps : ∀ p ∈ params, p.wf = true) (hrt : ∀ t ∈ rt, t.wf = true)
    (hbw : (Stmt.block bsp bs).wf T true false = true) :
    ∀ (s : ParseState) (ts bts rest : List Token), s.target = T → s.inFunction = false →
      s.rest = ts ++ bts ++ rest → s.left = s.rest.length →
      Touching ts (keywordWord "function" :: identWord name :: enclose "(" ")" (params.map Param.words) ++ rtWords rt) →
      (∀ y ∈ ts.tail, y.newlineBefore = false) → Laid bts (Stmt.block bsp bs).wordLines → rest ≠ [] →
      ∃ d' s', Parse.parseFunction start exported s = .ok d' s' ∧
        d'.erase = (Decl.function sp exported name params rt (.block bsp bs)).erase ∧ Leaves s s' rest := by
  intro s ts bts rest hT hF hs hl ht hn hb hr
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  obtain ⟨fk, ts₁, rfl, hfk, h₁⟩ := Touching.cons_one (by simpa [keywordWord] using ht)
  obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  obtain ⟨pts, rts, rfl, hpts, hrts⟩ := Touching.append_split h₂
  obtain ⟨lp, its, rp, rfl, hlp, hits, hrp⟩ := Touching.enclosed (by simpa [enclose] using hpts)
  -- The block starts with `{`.
  have hb' := hb
  simp only [Stmt.wordLines, Stmt.lines, List.map_cons] at hb'
  obtain ⟨ba, bb, rfl, hba, _⟩ := Laid.cons hb'
  obtain ⟨lb, ba', rfl, hlb, _⟩ := Touching.cons_one (by simpa [punctWord] using hba)
  have hnot1 : nm.kind ≠ .punct "*" := by rw [hnm]; simp
  have hnot2 : lp.kind ≠ .punct "<" := by rw [hlp]; exact punct_ne (by decide)
  have hn' : ∀ y ∈ its, y.newlineBefore = false := fun y hy => hn y (by simp [hy])
  cases rt with
  | none =>
    simp [rtWords, Touching] at hrts; subst hrts
    have hs' : s.rest = fk :: nm :: lp :: (its ++ rp :: (lb :: ba' ++ bb ++ rest)) := by simpa using hs
    let s₁ := advanced s fk nm (lp :: (its ++ rp :: (lb :: ba' ++ bb ++ rest)))
    let s₂ := advanced s₁ nm lp (its ++ rp :: (lb :: ba' ++ bb ++ rest))
    let s₃ : ParseState := { s₂ with rest := its ++ rp :: (lb :: ba' ++ bb ++ rest), left := s₂.left - 1, lastStop := lp.span.stop }
    have hl₃ : s₃.left = s₃.rest.length := by simp [s₃, s₂, s₁, hl, hs']
    obtain ⟨res, s₄, hit, hes, hL₄⟩ := params_reads params hps s₃ its (lb :: ba' ++ bb ++ rest) rp hT rfl hrp hl₃
      hits hn'
    have hs₄ : s₄.rest = rp :: (lb :: ba' ++ bb ++ rest) := hL₄.rest_eq
    let s₅ : ParseState := { s₄ with rest := lb :: ba' ++ bb ++ rest, left := s₄.left - 1, lastStop := rp.span.stop }
    have hs₅ : s₅.rest = lb :: (ba' ++ bb ++ rest) := by simp [s₅]
    let s₆ : ParseState := { s₅ with inFunction := true }
    have hl₆ : s₆.left = s₆.rest.length := by simp [s₆, s₅, hL₄.left_eq, hs₄]
    obtain ⟨body', s₇, hpb, heb, hL₇⟩ := parseBlock_budget (loop := false) bsp bs hbw s₆ (lb :: ba' ++ bb) rest
      (hL₄.target_eq.trans hT) rfl (fun h => by cases h) (by simp [s₆, s₅]) hl₆ hb hr
    have hc : lb.kind ≠ .punct ":" := by rw [hlb]; exact punct_ne (by decide)
    refine ⟨.function ⟨start, s₇.lastStop⟩ exported name res.toList none body', { s₇ with inFunction := false },
      ?_, ?_, ?_⟩
    · simp only [Parse.parseFunction]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
      rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hnot1] at h)]
      rw [Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname'), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
      rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hnot2] at h)]
      rw [Parse.bind_eq (Parse.expectPunct_ok (s := s₂) rfl (by simp) hlp), Parse.bind_eq (Parse.budget_eq _),
        Parse.bind_eq hit, Parse.bind_eq (Parse.expectPunct_ok hs₄ (by simp) hrp),
        Parse.bind_eq (Parse.peek_eq hs₅)]
      rw [if_neg (by simp [Token.isPunct, hc]), Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₅)]
      rw [if_pos (by simp [Token.isPunct, hlb]), Parse.pure_bind]
      rw [Parse.bind_eq (Parse.modify_eq _ _), Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpb,
        Parse.bind_eq (Parse.modify_eq _ _), Parse.bind_eq (Parse.spanFrom_eq _ _)]
      rfl
    · simp [Decl.erase, heb, Param.erase] at hes ⊢
      exact hes
    · exact leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₁) rfl (by simp [s₁, hl, hs']))
        (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])) (leaves_trans hL₄
          (leaves_trans (leaves_advance hs₄ (by rw [hL₄.left_eq, hs₄]))
            (leaves_inFunction (by simp [s₅, hL₄.inFunction_eq, s₃, s₂, s₁, hF]) hL₇)))))
  | some t =>
    have htw : t.wf = true := hrt t rfl
    obtain ⟨colon, tts, rfl, hcolon, htt⟩ := Touching.cons_one (by simpa [rtWords, punctWord] using hrts)
    have hs' : s.rest = fk :: nm :: lp :: (its ++ rp :: (colon :: (tts ++ (lb :: ba' ++ bb ++ rest)))) := by
      simpa using hs
    let s₁ := advanced s fk nm (lp :: (its ++ rp :: (colon :: (tts ++ (lb :: ba' ++ bb ++ rest)))))
    let s₂ := advanced s₁ nm lp (its ++ rp :: (colon :: (tts ++ (lb :: ba' ++ bb ++ rest))))
    let s₃ : ParseState := { s₂ with rest := its ++ rp :: (colon :: (tts ++ (lb :: ba' ++ bb ++ rest))), left := s₂.left - 1, lastStop := lp.span.stop }
    have hl₃ : s₃.left = s₃.rest.length := by simp [s₃, s₂, s₁, hl, hs']
    obtain ⟨res, s₄, hit, hes, hL₄⟩ := params_reads params hps s₃ its (colon :: (tts ++ (lb :: ba' ++ bb ++ rest)))
      rp hT rfl hrp hl₃ hits hn'
    have hs₄ : s₄.rest = rp :: (colon :: (tts ++ (lb :: ba' ++ bb ++ rest))) := hL₄.rest_eq
    let s₅ : ParseState := { s₄ with rest := colon :: (tts ++ (lb :: ba' ++ bb ++ rest)), left := s₄.left - 1, lastStop := rp.span.stop }
    let s₅' : ParseState := { s₅ with rest := tts ++ (lb :: ba' ++ bb ++ rest), left := s₅.left - 1, lastStop := colon.span.stop }
    have hl₅' : s₅'.left = s₅'.rest.length := by simp [s₅', s₅, hL₄.left_eq, hs₄]
    obtain ⟨t', s₆, hpt, het, hL₆⟩ := parseType_budget t htw s₅' tts (lb :: ba' ++ bb ++ rest) rfl hl₅' htt.kinds
      (fun y hy => hn y (by simp [hy])) (by simp) (followsType_punct hlb (by simp))
    have hs₆ : s₆.rest = lb :: (ba' ++ bb ++ rest) := by simpa using hL₆.rest_eq
    let s₇ : ParseState := { s₆ with inFunction := true }
    have hl₇ : s₇.left = s₇.rest.length := by simp [s₇, hL₆.left_eq, hL₆.rest_eq]
    obtain ⟨body', s₈, hpb, heb, hL₈⟩ := parseBlock_budget (loop := false) bsp bs hbw s₇ (lb :: ba' ++ bb) rest
      (by simp [s₇, hL₆.target_eq, s₅', s₅, hL₄.target_eq, s₃, s₂, s₁, hT]) rfl (fun h => by cases h)
      (by simpa [s₇] using hL₆.rest_eq) hl₇ hb hr
    refine ⟨.function ⟨start, s₈.lastStop⟩ exported name res.toList (some t') body', { s₈ with inFunction := false },
      ?_, ?_, ?_⟩
    · simp only [Parse.parseFunction]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
      rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hnot1] at h)]
      rw [Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname'), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
      rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hnot2] at h)]
      rw [Parse.bind_eq (Parse.expectPunct_ok (s := s₂) rfl (by simp) hlp), Parse.bind_eq (Parse.budget_eq _),
        Parse.bind_eq hit, Parse.bind_eq (Parse.expectPunct_ok hs₄ (by simp) hrp),
        Parse.bind_eq (Parse.peek_eq (s := s₅) rfl)]
      rw [if_pos (by simp [Token.isPunct, hcolon])]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₅) rfl (by simp))),
        Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpt, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₆)]
      rw [if_pos (by simp [Token.isPunct, hlb]), Parse.pure_bind]
      rw [Parse.bind_eq (Parse.modify_eq _ _), Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpb,
        Parse.bind_eq (Parse.modify_eq _ _), Parse.bind_eq (Parse.spanFrom_eq _ _)]
      rfl
    · simp [Decl.erase, heb, het, Param.erase] at hes ⊢
      exact hes
    · exact leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₁) rfl (by simp [s₁, hl, hs']))
        (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])) (leaves_trans hL₄
          (leaves_trans (leaves_advance hs₄ (by rw [hL₄.left_eq, hs₄]))
            (leaves_trans (leaves_advance (s := s₅) rfl (by simp [s₅, hL₄.left_eq, hs₄]))
              (leaves_trans hL₆ (leaves_inFunction (by simp [hL₆.inFunction_eq, s₅', s₅, hL₄.inFunction_eq, s₃, s₂, s₁, hF]) hL₈)))))))

/-! ### Type aliases -/

/-- `type`, a name, `=`, a type and `;`. -/
theorem parseTypeAlias_reads (start : Pos) (exported : Bool) (sp : Span) (name : String) (ty : TypeExpr)
    (hname : exprName name = true) (hty : ty.wf = true) :
    ∀ (s : ParseState) (ts rest : List Token), s.rest = ts ++ rest → s.left = s.rest.length →
      Touching ts (identWord "type" :: identWord name :: punctWord "=" :: ty.words ++ [punctWord ";"]) →
      (∀ y ∈ ts.tail, y.newlineBefore = false) → rest ≠ [] →
      ∃ d' s', Parse.parseTypeAlias start exported s = .ok d' s' ∧
        d'.erase = (Decl.typeAlias sp exported name ty).erase ∧ Leaves s s' rest := by
  intro s ts rest hs hl ht hn hr
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  obtain ⟨tk, ts₁, rfl, htk, h₁⟩ := Touching.cons_one (by simpa [identWord] using ht)
  obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  obtain ⟨eq, ts₃, rfl, heq, h₃⟩ := Touching.cons_one (by simpa [punctWord] using h₂)
  obtain ⟨tts, ts₄, rfl, htt, h₄⟩ := Touching.append_split h₃
  obtain ⟨semi, ts₅, rfl, hsemi, h₅⟩ := Touching.cons_one (by simpa [punctWord] using h₄)
  simp [Touching] at h₅; subst h₅
  have hs' : s.rest = tk :: nm :: eq :: (tts ++ semi :: rest) := by simpa using hs
  let s₁ := advanced s tk nm (eq :: (tts ++ semi :: rest))
  let s₂ := advanced s₁ nm eq (tts ++ semi :: rest)
  let s₃ : ParseState := { s₂ with rest := tts ++ semi :: rest, left := s₂.left - 1, lastStop := eq.span.stop }
  have hl₃ : s₃.left = s₃.rest.length := by simp [s₃, s₂, s₁, hl, hs']
  obtain ⟨t', s₄, hpt, het, hL₄⟩ := parseType_budget ty hty s₃ tts (semi :: rest) rfl hl₃ htt.kinds
    (fun y hy => hn y (by simp [hy])) (by simp) (followsType_eq_semi (.inr hsemi))
  have hs₄ : s₄.rest = semi :: rest := hL₄.rest_eq
  have hnot : eq.kind ≠ .punct "<" := by rw [heq]; exact punct_ne (by decide)
  refine ⟨.typeAlias ⟨start, semi.span.stop⟩ exported name t',
    { s₄ with rest := rest, left := s₄.left - 1, lastStop := semi.span.stop }, ?_, by simp [Decl.erase, het],
    leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])) (leaves_trans hL₄
        (leaves_advance hs₄ (by rw [hL₄.left_eq, hs₄])))))⟩
  simp only [Parse.parseTypeAlias]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname'),
    Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
  rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hnot] at h)]
  rw [Parse.bind_eq (Parse.expectPunct_ok (s := s₂) rfl (by simp) heq), Parse.bind_eq (Parse.budget_eq _),
    Parse.bind_eq hpt, Parse.bind_eq (endStatement_semi hs₄ hr hsemi), Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl

/-! ### The second token of an expression -/

/-- A token kind that is not a name. -/
def NotIdent (k : TokenKind) : Prop := ∀ m, k ≠ .ident m

/-- The second token of `a ++ b` is the second of `a`, or the first of `b`. -/
theorem second_append {a b : List TokenKind} {k₀ : TokenKind} {bs : List TokenKind} (hb : b = k₀ :: bs)
    (hk₀ : NotIdent k₀) (ha : a ≠ [])
    (IH : ∀ {n k r}, a = .ident n :: k :: r → NotIdent k) :
    ∀ {n k r}, a ++ b = .ident n :: k :: r → NotIdent k := by
  intro n k r h
  subst hb
  cases a with
  | nil => exact absurd rfl ha
  | cons x a' =>
    cases a' with
    | nil => simp at h; obtain ⟨_, rfl, _⟩ := h; exact hk₀
    | cons y a'' => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact IH rfl

theorem Expr.tokens_ne_nil (e : Expr) : e.tokens ≠ [] := by
  obtain ⟨k, hk, _⟩ := Expr.first e; intro h; rw [h] at hk; simp at hk

theorem notIdent_binOp (op : BinOp) : ∃ k ks, symbol op.symbol = k :: ks ∧ NotIdent k := by
  cases op <;> simp [BinOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord, NotIdent]

theorem notIdent_assignOp (op : AssignOp) : ∃ k ks, symbol op.symbol = k :: ks ∧ NotIdent k := by
  cases op <;> simp [AssignOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord, NotIdent]

/-- An expression that starts with a name has no name as its second token: an
operator, a `.`, a `(` or a `[` follows the name, if anything does. -/
theorem Expr.second : ∀ (e : Expr) {n : String} {k : TokenKind} {r : List TokenKind},
    e.tokens = .ident n :: k :: r → NotIdent k
  | .member sp o p, _, _, _, h => by
    rw [Expr.tokens_member] at h
    exact second_append rfl (by simp [NotIdent]) (Expr.tokens_ne_nil o) (fun h' => Expr.second o h') h
  | .index sp o i, _, _, _, h => by
    rw [Expr.tokens_index, List.append_assoc] at h
    exact second_append rfl (by simp [NotIdent]) (Expr.tokens_ne_nil o) (fun h' => Expr.second o h') h
  | .call sp c as, _, _, _, h => by
    rw [Expr.tokens_call, List.append_assoc] at h
    exact second_append rfl (by simp [NotIdent]) (Expr.tokens_ne_nil c) (fun h' => Expr.second c h') h
  | .postfix sp op a, _, _, _, h => by
    rw [Expr.tokens_postfix] at h
    exact second_append rfl (by simp [NotIdent]) (Expr.tokens_ne_nil a) (fun h' => Expr.second a h') h
  | .binary sp op l r', _, _, _, h => by
    rw [Expr.tokens_binary, List.append_assoc] at h
    obtain ⟨k₀, ks, hk, hn⟩ := notIdent_binOp op
    exact second_append (by rw [hk]; rfl) hn (Expr.tokens_ne_nil l) (fun h' => Expr.second l h') h
  | .cond sp t a b, _, _, _, h => by
    rw [Expr.tokens_cond, List.append_assoc] at h
    exact second_append rfl (by simp [NotIdent]) (Expr.tokens_ne_nil t) (fun h' => Expr.second t h') h
  | .assign sp op t v, _, _, _, h => by
    rw [Expr.tokens_assign, List.append_assoc] at h
    obtain ⟨k₀, ks, hk, hn⟩ := notIdent_assignOp op
    exact second_append (by rw [hk]; rfl) hn (Expr.tokens_ne_nil t) (fun h' => Expr.second t h') h
  | .ident .., _, _, _, h | .number .., _, _, _, h | .bigint .., _, _, _, h | .string .., _, _, _, h
  | .null _, _, _, _, h => by simp [Expr.tokens, Expr.words, identWord, keywordWord] at h
  | .bool _ b, _, _, _, h => by cases b <;> simp [Expr.tokens, Expr.words, keywordWord] at h
  | .array .., _, _, _, h => by simp [Expr.tokens_array] at h
  | .object .., _, _, _, h => by simp [Expr.tokens_object] at h
  | .paren .., _, _, _, h => by simp [Expr.tokens_paren] at h
  | .unary _ op _, _, _, _, h => by
    rw [Expr.tokens_unary] at h
    cases op <;> simp [UnaryOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord] at h
  | .prefix .., _, _, _, h => by simp [Expr.tokens_prefix] at h


/-! ### Fields of an interface -/

/-- What `Decl.erase` does to a field. -/
def Field.erase (f : Field) : Field := { f with span := noSpan, type := f.type.erase }

/-- `name: T;`, without `readonly` and `?`. -/
theorem parseField_plain (sp : Span) (name : String) (ty : TypeExpr) (hty : ty.wf = true)
    (s : ParseState) (ts rest : List Token) (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length)
    (ht : Touching ts (Field.words ⟨sp, false, name, false, ty⟩)) (hn : ∀ y ∈ ts.tail, y.newlineBefore = false)
    (hr : rest ≠ []) :
    ∃ f' s', Parse.parseField s = .ok f' s' ∧ f'.erase = Field.erase ⟨sp, false, name, false, ty⟩ ∧
      Leaves s s' rest := by
  simp only [Field.words, Bool.false_eq_true, ↓reduceIte, List.nil_append] at ht
  obtain ⟨nm, ts₁, rfl, hnm, h₁⟩ : ∃ nm ts₁, ts = nm :: ts₁ ∧ [nm.kind] = propertyName name ∧
      Touching ts₁ (punctWord ":" :: ty.words ++ [punctWord ";"]) := by
    obtain ⟨a, b, rfl, ha, _, hb⟩ := ht
    have hlen := congrArg List.length ha
    rw [List.length_map, length_propertyName] at hlen
    match a, ha with
    | [nm], ha => exact ⟨nm, b, rfl, by simpa using ha, hb⟩
  obtain ⟨c, ts₂, rfl, hc, h₂⟩ := Touching.cons_one (by simpa [punctWord] using h₁)
  obtain ⟨tts, ts₃, rfl, htt, h₃⟩ := Touching.append_split h₂
  obtain ⟨semi, ts₄, rfl, hsemi, h₄⟩ := Touching.cons_one (by simpa [punctWord] using h₃)
  simp [Touching] at h₄; subst h₄
  have hs' : s.rest = nm :: c :: (tts ++ semi :: rest) := by simpa using hs
  let s₁ := advanced s nm c (tts ++ semi :: rest)
  let s₂ : ParseState := { s₁ with rest := tts ++ semi :: rest, left := s₁.left - 1, lastStop := c.span.stop }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁, hl, hs']
  obtain ⟨t', s₃, hpt, het, hL₃⟩ := parseType_budget ty hty s₂ tts (semi :: rest) rfl hl₂ htt.kinds
    (fun y hy => hn y (by simp [hy])) (by simp) (followsType_eq_semi (.inr hsemi))
  have hs₃ : s₃.rest = semi :: rest := hL₃.rest_eq
  have hc1 : (c.kind == .punct "?") = false := by simp [hc]
  have hc2 : (c.kind == .punct "(") = false := by simp [hc]
  have hc3 : (c.kind == .punct "<") = false := by simp [hc]
  refine ⟨⟨⟨nm.span.start, semi.span.stop⟩, false, name, false, t'⟩,
    { s₃ with rest := rest, left := s₃.left - 1, lastStop := semi.span.stop }, ?_, by simp [Field.erase, het],
    leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans hL₃ (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃]))))⟩
  simp only [Parse.parseField]
  rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.peekAt_rest _ _)]
  simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent, hc,
    Bool.and_false, Bool.or_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind]
  rw [Parse.bind_eq (readPropertyName_ok hs' hnm), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
  rw [if_neg (show ¬ (c.isPunct "?" = true) by simp [Token.isPunct, hc]), Parse.pure_bind,
    Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
  rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hc] at h)]
  rw [if_pos (show c.isPunct ":" = true by simp [Token.isPunct, hc]), Parse.pure_bind]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₁) rfl (by simp))), Parse.bind_eq (Parse.budget_eq _),
    Parse.bind_eq hpt, Parse.bind_eq (Parse.peek_eq hs₃)]
  rw [if_pos (show (semi.isPunct ";" || semi.isPunct ",") = true by simp [Token.isPunct, hsemi])]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs₃ hr)), Parse.bind_eq (Parse.spanFrom_eq _ _)]
  simp [Token.isPunct, hc, pure, EStateM.pure]


/-- `name?: T;`. -/
theorem parseField_opt (sp : Span) (name : String) (ty : TypeExpr) (hty : ty.wf = true)
    (s : ParseState) (ts rest : List Token) (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length)
    (ht : Touching ts (Field.words ⟨sp, false, name, true, ty⟩)) (hn : ∀ y ∈ ts.tail, y.newlineBefore = false)
    (hr : rest ≠ []) :
    ∃ f' s', Parse.parseField s = .ok f' s' ∧ f'.erase = Field.erase ⟨sp, false, name, true, ty⟩ ∧
      Leaves s s' rest := by
  simp only [Field.words, Bool.false_eq_true, ↓reduceIte, List.nil_append] at ht
  obtain ⟨nm, ts₁, rfl, hnm, h₁⟩ : ∃ nm ts₁, ts = nm :: ts₁ ∧ [nm.kind] = propertyName name ∧
      Touching ts₁ (punctWord "?" :: punctWord ":" :: ty.words ++ [punctWord ";"]) := by
    obtain ⟨a, b, rfl, ha, _, hb⟩ := ht
    have hlen := congrArg List.length ha
    rw [List.length_map, length_propertyName] at hlen
    match a, ha with
    | [nm], ha => exact ⟨nm, b, rfl, by simpa using ha, hb⟩
  obtain ⟨q, ts₀, rfl, hq, h₀⟩ := Touching.cons_one (by simpa [punctWord] using h₁)
  obtain ⟨c, ts₂, rfl, hc, h₂⟩ := Touching.cons_one (by simpa [punctWord] using h₀)
  obtain ⟨tts, ts₃, rfl, htt, h₃⟩ := Touching.append_split h₂
  obtain ⟨semi, ts₄, rfl, hsemi, h₄⟩ := Touching.cons_one (by simpa [punctWord] using h₃)
  simp [Touching] at h₄; subst h₄
  have hs' : s.rest = nm :: q :: c :: (tts ++ semi :: rest) := by simpa using hs
  let s₁ := advanced s nm q (c :: (tts ++ semi :: rest))
  let s₁' := advanced s₁ q c (tts ++ semi :: rest)
  let s₂ : ParseState := { s₁' with rest := tts ++ semi :: rest, left := s₁'.left - 1, lastStop := c.span.stop }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁', s₁, hl, hs']
  obtain ⟨t', s₃, hpt, het, hL₃⟩ := parseType_budget ty hty s₂ tts (semi :: rest) rfl hl₂ htt.kinds
    (fun y hy => hn y (by simp [hy])) (by simp) (followsType_eq_semi (.inr hsemi))
  have hs₃ : s₃.rest = semi :: rest := hL₃.rest_eq
  refine ⟨⟨⟨nm.span.start, semi.span.stop⟩, false, name, true, t'⟩,
    { s₃ with rest := rest, left := s₃.left - 1, lastStop := semi.span.stop }, ?_, by simp [Field.erase, het],
    leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₁') rfl (by simp [s₁', s₁, hl, hs']))
        (leaves_trans hL₃ (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃])))))⟩
  simp only [Parse.parseField]
  rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.peekAt_rest _ _)]
  simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent, hq,
    Bool.and_false, Bool.or_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind]
  rw [Parse.bind_eq (readPropertyName_ok hs' hnm), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
  rw [if_pos (show q.isPunct "?" = true by simp [Token.isPunct, hq]),
    Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₁) rfl)), Parse.bind_eq (Parse.peek_eq (s := s₁') rfl)]
  rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hc] at h)]
  rw [if_pos (show c.isPunct ":" = true by simp [Token.isPunct, hc]), Parse.pure_bind]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₁') rfl (by simp))), Parse.bind_eq (Parse.budget_eq _),
    Parse.bind_eq hpt, Parse.bind_eq (Parse.peek_eq hs₃)]
  rw [if_pos (show (semi.isPunct ";" || semi.isPunct ",") = true by simp [Token.isPunct, hsemi])]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs₃ hr)), Parse.bind_eq (Parse.spanFrom_eq _ _)]
  simp [Token.isPunct, hc, hq, pure, EStateM.pure]

/-- `readonly name: T;` or `readonly name?: T;`. -/
theorem parseField_ro (sp : Span) (name : String) (opt : Bool) (ty : TypeExpr) (hty : ty.wf = true)
    (s : ParseState) (ts rest : List Token) (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length)
    (ht : Touching ts (Field.words ⟨sp, true, name, opt, ty⟩)) (hn : ∀ y ∈ ts.tail, y.newlineBefore = false)
    (hr : rest ≠ []) :
    ∃ f' s', Parse.parseField s = .ok f' s' ∧ f'.erase = Field.erase ⟨sp, true, name, opt, ty⟩ ∧
      Leaves s s' rest := by
  simp only [Field.words, ↓reduceIte] at ht
  obtain ⟨ro, ts₀, rfl, hro, ht'⟩ := Touching.cons_one (by simpa [identWord] using ht)
  obtain ⟨nm, ts₁, rfl, hnm, h₁⟩ : ∃ nm ts₁, ts₀ = nm :: ts₁ ∧ [nm.kind] = propertyName name ∧
      Touching ts₁ ((if opt = true then [punctWord "?"] else []) ++ punctWord ":" :: (ty.words ++ [punctWord ";"])) := by
    obtain ⟨a, b, rfl, ha, _, hb⟩ := ht'
    have hlen := congrArg List.length ha
    rw [List.length_map, length_propertyName] at hlen
    match a, ha with
    | [nm], ha => exact ⟨nm, b, rfl, by simpa using ha, hb⟩
  have hnmk : nm.kind = .keyword name ∨ nm.kind = .ident name := by
    unfold propertyName at hnm; split at hnm <;> simp [keywordWord, identWord] at hnm <;> simp [hnm]
  have hnmn : nm.newlineBefore = false := hn nm (by simp)
  cases opt with
  | false =>
    obtain ⟨c, ts₂, rfl, hc, h₂⟩ := Touching.cons_one (by simpa [punctWord] using h₁)
    obtain ⟨tts, ts₃, rfl, htt, h₃⟩ := Touching.append_split h₂
    obtain ⟨semi, ts₄, rfl, hsemi, h₄⟩ := Touching.cons_one (by simpa [punctWord] using h₃)
    simp [Touching] at h₄; subst h₄
    have hs' : s.rest = ro :: nm :: c :: (tts ++ semi :: rest) := by simpa using hs
    let s₀ := advanced s ro nm (c :: (tts ++ semi :: rest))
    let s₁ := advanced s₀ nm c (tts ++ semi :: rest)
    let s₂ : ParseState := { s₁ with rest := tts ++ semi :: rest, left := s₁.left - 1, lastStop := c.span.stop }
    have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁, s₀, hl, hs']
    obtain ⟨t', s₃, hpt, het, hL₃⟩ := parseType_budget ty hty s₂ tts (semi :: rest) rfl hl₂ htt.kinds
      (fun y hy => hn y (by simp [hy])) (by simp) (followsType_eq_semi (.inr hsemi))
    have hs₃ : s₃.rest = semi :: rest := hL₃.rest_eq
    refine ⟨⟨⟨ro.span.start, semi.span.stop⟩, true, name, false, t'⟩,
      { s₃ with rest := rest, left := s₃.left - 1, lastStop := semi.span.stop }, ?_, by simp [Field.erase, het],
      leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₀) rfl (by simp [s₀, hl, hs']))
        (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, s₀, hl, hs']))
          (leaves_trans hL₃ (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃])))))⟩
    simp only [Parse.parseField]
    rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.peekAt_rest _ _)]
    rcases hnmk with hnmk | hnmk
    all_goals
      simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent, Token.isIdent,
        hro, hnmk, hnmn, beq_self_eq_true, Bool.true_and, Bool.not_false, Bool.true_or, Bool.or_true, Bool.and_true,
        ↓reduceIte]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (readPropertyName_ok (s := s₀) rfl hnm),
        Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
      rw [if_neg (show ¬ (c.isPunct "?" = true) by simp [Token.isPunct, hc]), Parse.pure_bind,
        Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
      rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hc] at h)]
      rw [if_pos (show c.isPunct ":" = true by simp [Token.isPunct, hc]), Parse.pure_bind]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₁) rfl (by simp))), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_eq hpt, Parse.bind_eq (Parse.peek_eq hs₃)]
      rw [if_pos (show (semi.isPunct ";" || semi.isPunct ",") = true by simp [Token.isPunct, hsemi])]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs₃ hr)), Parse.bind_eq (Parse.spanFrom_eq _ _)]
      simp [Token.isPunct, hc, pure, EStateM.pure]
  | true =>
    obtain ⟨q, ts₀', rfl, hq, h₀⟩ := Touching.cons_one (by simpa [punctWord] using h₁)
    obtain ⟨c, ts₂, rfl, hc, h₂⟩ := Touching.cons_one (by simpa [punctWord] using h₀)
    obtain ⟨tts, ts₃, rfl, htt, h₃⟩ := Touching.append_split h₂
    obtain ⟨semi, ts₄, rfl, hsemi, h₄⟩ := Touching.cons_one (by simpa [punctWord] using h₃)
    simp [Touching] at h₄; subst h₄
    have hs' : s.rest = ro :: nm :: q :: c :: (tts ++ semi :: rest) := by simpa using hs
    let s₀ := advanced s ro nm (q :: c :: (tts ++ semi :: rest))
    let s₁ := advanced s₀ nm q (c :: (tts ++ semi :: rest))
    let s₁' := advanced s₁ q c (tts ++ semi :: rest)
    let s₂ : ParseState := { s₁' with rest := tts ++ semi :: rest, left := s₁'.left - 1, lastStop := c.span.stop }
    have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁', s₁, s₀, hl, hs']
    obtain ⟨t', s₃, hpt, het, hL₃⟩ := parseType_budget ty hty s₂ tts (semi :: rest) rfl hl₂ htt.kinds
      (fun y hy => hn y (by simp [hy])) (by simp) (followsType_eq_semi (.inr hsemi))
    have hs₃ : s₃.rest = semi :: rest := hL₃.rest_eq
    refine ⟨⟨⟨ro.span.start, semi.span.stop⟩, true, name, true, t'⟩,
      { s₃ with rest := rest, left := s₃.left - 1, lastStop := semi.span.stop }, ?_, by simp [Field.erase, het],
      leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₀) rfl (by simp [s₀, hl, hs']))
        (leaves_trans (leaves_advanced (s := s₁) rfl (by simp [s₁, s₀, hl, hs']))
          (leaves_trans (leaves_advance (s := s₁') rfl (by simp [s₁', s₁, s₀, hl, hs']))
            (leaves_trans hL₃ (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃]))))))⟩
    simp only [Parse.parseField]
    rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.peekAt_rest _ _)]
    rcases hnmk with hnmk | hnmk
    all_goals
      simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent, Token.isIdent,
        hro, hnmk, hnmn, beq_self_eq_true, Bool.true_and, Bool.not_false, Bool.true_or, Bool.or_true, Bool.and_true,
        ↓reduceIte]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (readPropertyName_ok (s := s₀) rfl hnm),
        Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
      rw [if_pos (show q.isPunct "?" = true by simp [Token.isPunct, hq]),
        Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₁) rfl)), Parse.bind_eq (Parse.peek_eq (s := s₁') rfl)]
      rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hc] at h)]
      rw [if_pos (show c.isPunct ":" = true by simp [Token.isPunct, hc]), Parse.pure_bind]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₁') rfl (by simp))), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_eq hpt, Parse.bind_eq (Parse.peek_eq hs₃)]
      rw [if_pos (show (semi.isPunct ";" || semi.isPunct ",") = true by simp [Token.isPunct, hsemi])]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs₃ hr)), Parse.bind_eq (Parse.spanFrom_eq _ _)]
      simp [Token.isPunct, hc, hq, pure, EStateM.pure]


/-- A field of an interface: `readonly` or not, a name, `?` or not, `:`, a type and `;`. -/
theorem parseField_reads (f : Field) (hty : f.type.wf = true) (s : ParseState) (ts rest : List Token)
    (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length) (ht : Touching ts f.words)
    (hn : ∀ y ∈ ts.tail, y.newlineBefore = false) (hr : rest ≠ []) :
    ∃ f' s', Parse.parseField s = .ok f' s' ∧ f'.erase = f.erase ∧ Leaves s s' rest := by
  obtain ⟨sp, ro, name, opt, ty⟩ := f
  cases ro with
  | true => exact parseField_ro sp name opt ty hty s ts rest hs hl ht hn hr
  | false =>
    cases opt with
    | false => exact parseField_plain sp name ty hty s ts rest hs hl ht hn hr
    | true => exact parseField_opt sp name ty hty s ts rest hs hl ht hn hr

/-! ### Interfaces -/

/-- A field starts with `readonly` or its name, so not with `}` and not at the end of the file. -/
theorem Field.first (f : Field) : ∃ k, f.words.flatten.head? = some k ∧ k ≠ .punct "}" ∧ k ≠ .eof := by
  obtain ⟨sp, ro, name, opt, ty⟩ := f
  cases ro with
  | true => exact ⟨.ident "readonly", by simp [Field.words, identWord], by simp, by simp⟩
  | false =>
    by_cases h : name ∈ Lex.reservedWords
    · exact ⟨.keyword name, by simp [Field.words, propertyName, h, keywordWord], by simp, by simp⟩
    · exact ⟨.ident name, by simp [Field.words, propertyName, h, identWord], by simp, by simp⟩

/-- The loop of `parseInterface` reads the fields of an interface, one on each line, which a `}` follows. -/
theorem field_loop :
    ∀ (fields : List Field) (fuel : Nat) (acc : Array Field) (s : ParseState) (ts rest : List Token) (c : Token),
      (∀ f ∈ fields, f.type.wf = true) → fields.length < fuel →
      s.rest = ts ++ c :: rest → c.kind = .punct "}" → s.left = s.rest.length →
      Laid ts (fields.map Field.words) →
      ∃ res s', Parse.iterate fuel acc (Parse.blockStep Parse.parseField) s = .ok res s' ∧
        res.toList.map Field.erase = (acc.toList ++ fields).map Field.erase ∧ Leaves s s' (c :: rest) := by
  intro fields
  induction fields with
  | nil =>
    intro fuel acc s ts rest c _ hlen hs hc hl ht
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    simp [Laid] at ht; subst ht
    have hs' : s.rest = c :: rest := by simpa using hs
    refine ⟨acc, s, Parse.iterate_false ?_, by simp, ⟨hs', by simp [hl, hs'], rfl, rfl, rfl, rfl⟩⟩
    simp only [Parse.blockStep]
    rw [Parse.bind_eq (Parse.peek_eq hs')]
    simp [Token.isPunct, hc, pure, EStateM.pure]
  | cons f fields ih =>
    intro fuel acc s ts rest c hw hlen hs hc hl ht
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    obtain ⟨a, b, rfl, ha, hna, _, hb⟩ := Laid.cons (by simpa using ht)
    obtain ⟨k, hk, hk1, hk2⟩ := Field.first f
    obtain ⟨x, a', rfl, hx⟩ : ∃ x a', a = x :: a' ∧ x.kind = k := by
      have hk' : (a.map (·.kind)).head? = some k := by rw [ha.kinds]; exact hk
      cases a with
      | nil => simp at hk'
      | cons x a' => simp at hk'; exact ⟨x, a', rfl, hk'⟩
    have hs' : s.rest = x :: (a' ++ (b ++ c :: rest)) := by simpa using hs
    obtain ⟨f₁, s₁, hp, he, hL₁⟩ := parseField_reads f (hw f (by simp)) s (x :: a') (b ++ c :: rest)
      (by simp [hs']) hl ha hna (by simp)
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL₁.left_eq, hL₁.rest_eq]
    obtain ⟨res, s', hit, he', hL'⟩ := ih f' (acc.push f₁) s₁ b rest c (fun g hg => hw g (by simp [hg]))
      (by simp at hlen; omega) hL₁.rest_eq hc hl₁ hb
    refine ⟨res, s', ?_, by rw [he']; simp [he], leaves_trans hL₁ hL'⟩
    rw [Parse.iterate_true (acc' := acc.push f₁) (s' := s₁)]
    · exact hit
    · have hb1 : (x.kind == .punct "}") = false := by simp [hx, hk1]
      have hb2 : (x.kind == .eof) = false := by simp [hx, hk2]
      simp only [Parse.blockStep]
      rw [Parse.bind_eq (Parse.peek_eq hs')]
      simp only [Token.isPunct, Token.isEof, hb1, hb2, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind]
      rw [Parse.bind_eq hp]
      rfl

theorem Laid.length_fields : ∀ {fields : List Field} {ts : List Token}, Laid ts (fields.map Field.words) →
    fields.length ≤ ts.length
  | [], _, _ => by simp
  | f :: fields, ts, h => by
    obtain ⟨a, b, rfl, ha, _, _, hb⟩ := Laid.cons (by simpa using h)
    obtain ⟨k, hk, _, _⟩ := Field.first f
    have : a ≠ [] := by
      intro e; subst e
      have h0 : f.words.flatten = [] := by have := ha.kinds; simpa using this.symm
      rw [h0] at hk; simp at hk
    have := Laid.length_fields hb
    cases a with
    | nil => exact absurd rfl ‹_›
    | cons _ _ => simp; omega


/-- `interface`, a name and `{`, the fields on their own lines, and `}`. -/
theorem parseInterface_reads (start : Pos) (exported : Bool) (sp : Span) (name : String) (fields : List Field)
    (hname : exprName name = true) (hfs : ∀ f ∈ fields, f.type.wf = true) :
    ∀ (s : ParseState) (ts fts rest : List Token) (rb : Token), s.rest = ts ++ fts ++ rb :: rest →
      s.left = s.rest.length → Touching ts [identWord "interface", identWord name, punctWord "{"] →
      Laid fts (fields.map Field.words) → rb.kind = .punct "}" → rest ≠ [] →
      ∃ d' s', Parse.parseInterface start exported s = .ok d' s' ∧
        d'.erase = (Decl.interface sp exported name fields).erase ∧ Leaves s s' rest := by
  intro s ts fts rest rb hs hl ht hf hrb hr
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  obtain ⟨it, ts₁, rfl, hit, h₁⟩ := Touching.cons_one (by simpa [identWord] using ht)
  obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  obtain ⟨lb, ts₃, rfl, hlb, h₃⟩ := Touching.cons_one (by simpa [punctWord] using h₂)
  simp [Touching] at h₃; subst h₃
  have hs' : s.rest = it :: nm :: lb :: (fts ++ rb :: rest) := by simpa using hs
  let s₁ := advanced s it nm (lb :: (fts ++ rb :: rest))
  let s₂ := advanced s₁ nm lb (fts ++ rb :: rest)
  let s₃ : ParseState := { s₂ with rest := fts ++ rb :: rest, left := s₂.left - 1, lastStop := lb.span.stop }
  have hl₃ : s₃.left = s₃.rest.length := by simp [s₃, s₂, s₁, hl, hs']
  have hlen := Laid.length_fields hf
  obtain ⟨res, s₄, hit', he, hL₄⟩ := field_loop fields (10 * (s₃.left + 1)) #[] s₃ fts rest rb hfs
    (by have : s₃.left = fts.length + rest.length + 1 := by simp [s₃, s₂, s₁, hl, hs']; omega
        omega) rfl hrb hl₃ hf
  have hs₄ : s₄.rest = rb :: rest := hL₄.rest_eq
  have hn1 : (lb.kind == .punct "<") = false := by simp [hlb]
  have hn2 : lb.kind ≠ .keyword "extends" := by rw [hlb]; simp
  refine ⟨.interface ⟨start, rb.span.stop⟩ exported name res.toList,
    { s₄ with rest := rest, left := s₄.left - 1, lastStop := rb.span.stop }, ?_, ?_,
    leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])) (leaves_trans hL₄
        (leaves_advance hs₄ (by rw [hL₄.left_eq, hs₄])))))⟩
  · simp only [Parse.parseInterface]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname'),
      Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hlb] at h),
      Parse.ite_guard (fun h => by simp [Token.isKeyword, hn2] at h)]
    rw [Parse.bind_eq (Parse.expectPunct_ok (s := s₂) rfl (by simp) hlb), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_eq hit', Parse.bind_eq (Parse.expectPunct_ok hs₄ hr hrb), Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · simp [Decl.erase, Field.erase] at he ⊢
    exact he


/-! ### Imports -/

/-- What `Decl.erase` does to an imported name. -/
def ImportName.erase (n : ImportName) : ImportName := { n with span := noSpan }

/-- The tokens of an imported name: `type` and the name, or the name. -/
theorem Touching.importName {ts : List Token} {n : ImportName} (h : Touching ts n.words) :
    (n.typeOnly = true ∧ ∃ ty nm, ts = [ty, nm] ∧ ty.kind = .ident "type" ∧ nm.kind = .ident n.name) ∨
    (n.typeOnly = false ∧ ∃ nm, ts = [nm] ∧ nm.kind = .ident n.name) := by
  obtain ⟨sp, typeOnly, name⟩ := n
  cases typeOnly with
  | true =>
    simp only [ImportName.words, ↓reduceIte] at h
    obtain ⟨ty, ts₁, rfl, hty, h₁⟩ := Touching.cons_one (by simpa [identWord] using h)
    obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
    simp [Touching] at h₂; subst h₂
    exact .inl ⟨rfl, ty, nm, rfl, hty, hnm⟩
  | false =>
    simp only [ImportName.words, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨nm, ts₁, rfl, hnm, h₁⟩ := Touching.cons_one (by simpa [identWord] using h)
    simp [Touching] at h₁; subst h₁
    exact .inr ⟨rfl, nm, rfl, hnm⟩

/-- One step of the loop of `parseImport`: a name, which a `,` or the `}` follows. -/
theorem importStep_ok {acc : Array ImportName} {s : ParseState} {n : ImportName} {a : List Token} {d : Token}
    {r : List Token} (hs : s.rest = a ++ d :: r) (hl : s.left = s.rest.length) (ha : Touching a n.words)
    (hname : n.name ∉ Parse.refusedNames) (hd : d.kind = .punct "," ∨ d.kind = .punct "}")
    (hr : d.kind = .punct "," → r ≠ []) :
    ∃ n' s', Parse.importStep false acc s = .ok (acc.push n', true) s' ∧ n'.erase = n.erase ∧
      Leaves s s' (if d.isPunct "," = true then r else d :: r) := by
  have hdi : ∀ m, d.kind ≠ .ident m := by rcases hd with h | h <;> intro m <;> rw [h] <;> simp
  have hd1 : (d.kind == .ident "as") = false := by simp [hdi]
  rcases Touching.importName ha with ⟨hto, ty, nm, rfl, hty, hnm⟩ | ⟨hto, nm, rfl, hnm⟩
  · have hs' : s.rest = ty :: nm :: d :: r := by simpa using hs
    let s₁ := advanced s ty nm (d :: r)
    let s₂ := advanced s₁ nm d r
    have hty1 : (ty.kind == .punct "}") = false := by simp [hty]
    rcases hd with hd | hd
    · refine ⟨⟨nm.span, true, n.name⟩, { s₂ with rest := r, left := s₂.left - 1, lastStop := d.span.stop }, ?_,
        by simp [ImportName.erase, hto], ?_⟩
      · simp only [Parse.importStep]
        rw [Parse.bind_eq (Parse.peek_eq hs')]
        rw [if_neg (show ¬ (ty.isPunct "}" = true) by simp [Token.isPunct, hty1]), Parse.pure_bind]
        rw [Parse.bind_eq (Parse.peekAt_rest _ _)]
        simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent,
          Token.isIdent, hty, hnm, hd1, beq_self_eq_true, Bool.true_and, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte, Parse.pure_bind, Bool.or_true, Bool.false_or]
        rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl),
          Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
        rw [if_neg (show ¬ ((d.kind == .ident "as") = true) by simp [hd1]), Parse.pure_bind,
          Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
        rw [if_pos (show d.isPunct "," = true by simp [Token.isPunct, hd]),
          Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₂) rfl (hr hd)))]
        rfl
      · simp only [Token.isPunct, hd, beq_self_eq_true, ↓reduceIte]
        exact leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advanced (s := s₁) rfl
          (by simp [s₁, hl, hs'])) (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])))
    · refine ⟨⟨nm.span, true, n.name⟩, s₂, ?_, by simp [ImportName.erase, hto], ?_⟩
      · simp only [Parse.importStep]
        rw [Parse.bind_eq (Parse.peek_eq hs')]
        rw [if_neg (show ¬ (ty.isPunct "}" = true) by simp [Token.isPunct, hty1]), Parse.pure_bind]
        rw [Parse.bind_eq (Parse.peekAt_rest _ _)]
        simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent,
          Token.isIdent, hty, hnm, hd1, beq_self_eq_true, Bool.true_and, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte, Parse.pure_bind, Bool.or_true, Bool.false_or]
        rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl),
          Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
        rw [if_neg (show ¬ ((d.kind == .ident "as") = true) by simp [hd1]), Parse.pure_bind,
          Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
        rw [if_neg (show ¬ (d.isPunct "," = true) by simp [Token.isPunct, hd]),
          if_neg (show ¬ ((!d.isPunct "}") = true) by simp [Token.isPunct, hd]), Parse.pure_bind]
        rfl
      · have : (d.kind == .punct ",") = false := by simp [hd]
        simp only [Token.isPunct, this, Bool.false_eq_true, ↓reduceIte]
        exact leaves_trans (leaves_advanced hs' hl) (leaves_advanced (s := s₁) rfl (by simp [s₁, hl, hs']))
  · have hs' : s.rest = nm :: d :: r := by simpa using hs
    let s₁ := advanced s nm d r
    have hnm1 : (nm.kind == .punct "}") = false := by simp [hnm]
    have hdA : d.isAnyIdent = false := by
      rcases hd with h | h <;> simp [Token.isAnyIdent, h]
    rcases hd with hd | hd
    · refine ⟨⟨nm.span, false, n.name⟩, { s₁ with rest := r, left := s₁.left - 1, lastStop := d.span.stop }, ?_,
        by simp [ImportName.erase, hto], ?_⟩
      · simp only [Parse.importStep]
        rw [Parse.bind_eq (Parse.peek_eq hs')]
        rw [if_neg (show ¬ (nm.isPunct "}" = true) by simp [Token.isPunct, hnm1]), Parse.pure_bind]
        rw [Parse.bind_eq (Parse.peekAt_rest _ _)]
        simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, hdA, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte, Parse.pure_bind, Bool.or_false]
        rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (readName_ok hs' hnm hname),
          Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
        rw [if_neg (show ¬ (d.isIdent "as" = true) by simp [Token.isIdent, hd1]), Parse.pure_bind,
          Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
        rw [if_pos (show d.isPunct "," = true by simp [Token.isPunct, hd]),
          Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₁) rfl (hr hd)))]
        rfl
      · simp only [Token.isPunct, hd, beq_self_eq_true, ↓reduceIte]
        exact leaves_trans (leaves_advanced hs' hl) (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
    · refine ⟨⟨nm.span, false, n.name⟩, s₁, ?_, by simp [ImportName.erase, hto], ?_⟩
      · simp only [Parse.importStep]
        rw [Parse.bind_eq (Parse.peek_eq hs')]
        rw [if_neg (show ¬ (nm.isPunct "}" = true) by simp [Token.isPunct, hnm1]), Parse.pure_bind]
        rw [Parse.bind_eq (Parse.peekAt_rest _ _)]
        simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, hdA, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte, Parse.pure_bind, Bool.or_false]
        rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (readName_ok hs' hnm hname),
          Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
        rw [if_neg (show ¬ (d.isIdent "as" = true) by simp [Token.isIdent, hd1]), Parse.pure_bind,
          Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
        rw [if_neg (show ¬ (d.isPunct "," = true) by simp [Token.isPunct, hd]),
          if_neg (show ¬ ((!d.isPunct "}") = true) by simp [Token.isPunct, hd]), Parse.pure_bind]
        rfl
      · have : (d.kind == .punct ",") = false := by simp [hd]
        simp only [Token.isPunct, this, Bool.false_eq_true, ↓reduceIte]
        exact leaves_advanced hs' hl

/-- The loop of `parseImport` reads the names of an import, with a `,` between two of them, which a `}` follows. -/
theorem import_loop :
    ∀ (names : List ImportName) (fuel : Nat) (acc : Array ImportName) (s : ParseState) (ts rest : List Token)
      (c : Token), (∀ n ∈ names, n.name ∉ Parse.refusedNames) → names.length < fuel →
      s.rest = ts ++ c :: rest → c.kind = .punct "}" → s.left = s.rest.length →
      Touching ts (commas (names.map ImportName.words)) →
      ∃ res s', Parse.iterate fuel acc (Parse.importStep false) s = .ok res s' ∧
        res.toList.map ImportName.erase = (acc.toList ++ names).map ImportName.erase ∧ Leaves s s' (c :: rest) := by
  intro names
  induction names with
  | nil =>
    intro fuel acc s ts rest c _ hlen hs hc hl ht
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    have hts : ts = [] := Touching.nil.mp (by simpa [commas] using ht)
    subst hts
    have hs' : s.rest = c :: rest := by simpa using hs
    refine ⟨acc, s, Parse.iterate_false ?_, by simp, ⟨hs', by simp [hl, hs'], rfl, rfl, rfl, rfl⟩⟩
    simp only [Parse.importStep]
    rw [Parse.bind_eq (Parse.peek_eq hs')]
    simp [Token.isPunct, hc, pure, EStateM.pure]
  | cons n names ih =>
    intro fuel acc s ts rest c hnames hlen hs hc hl ht
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    cases names with
    | nil =>
      have ha : Touching ts n.words := by simpa [commas] using ht
      obtain ⟨n', s₁, hstep, he, hL₁⟩ := importStep_ok (acc := acc) hs hl ha (hnames n (by simp)) (.inr hc)
        (fun h => absurd (hc.symm.trans h) (punct_ne (by decide)))
      have hc' : (c.kind == .punct ",") = false := by simp [hc]
      simp only [Token.isPunct, hc', Bool.false_eq_true, ↓reduceIte] at hL₁
      have hl₁ : s₁.left = s₁.rest.length := by rw [hL₁.left_eq, hL₁.rest_eq]
      obtain ⟨res, s', hit, he', hL'⟩ := ih f' (acc.push n') s₁ [] rest c (by simp) (by simp at hlen ⊢; omega)
        (by simpa using hL₁.rest_eq) hc hl₁ (by simp [commas, Touching])
      refine ⟨res, s', ?_, by rw [he']; simp [he], leaves_trans hL₁ hL'⟩
      rw [Parse.iterate_true hstep]; exact hit
    | cons y ys =>
      obtain ⟨a, more, rfl, ha, hmore⟩ := Touching.append_split (ws₁ := n.words)
        (ws₂ := punctWord "," :: commas ((y :: ys).map ImportName.words)) (by simpa [commas] using ht)
      obtain ⟨d, more', rfl, hd, hmore'⟩ := Touching.cons_one (by simpa [punctWord] using hmore)
      obtain ⟨n', s₁, hstep, he, hL₁⟩ := importStep_ok (acc := acc) (r := more' ++ c :: rest) (by simpa using hs)
        hl ha (hnames n (by simp)) (.inl hd) (fun _ => by simp)
      simp only [Token.isPunct, hd, beq_self_eq_true, ↓reduceIte] at hL₁
      have hl₁ : s₁.left = s₁.rest.length := by rw [hL₁.left_eq, hL₁.rest_eq]
      obtain ⟨res, s', hit, he', hL'⟩ := ih f' (acc.push n') s₁ more' rest c
        (fun m hm => hnames m (by simp at hm ⊢; rcases hm with h | h <;> simp [h]))
        (by simp at hlen ⊢; omega) hL₁.rest_eq hc hl₁ hmore'
      refine ⟨res, s', ?_, by rw [he']; simp [he], leaves_trans hL₁ hL'⟩
      rw [Parse.iterate_true hstep]; exact hit


/-- `import { names } from "source";`. -/
theorem parseImport_reads (start : Pos) (sp : Span) (names : List ImportName) (source : String)
    (hne : names ≠ []) (hnames : ∀ n ∈ names, n.name ∉ Parse.refusedNames) :
    ∀ (s : ParseState) (ts rest : List Token), s.rest = ts ++ rest → s.left = s.rest.length →
      Touching ts (keywordWord "import" :: enclose "{" "}" (names.map ImportName.words) ++
        [identWord "from", [.string source], punctWord ";"]) →
      (∀ y ∈ ts.tail, y.newlineBefore = false) → rest ≠ [] →
      ∃ d' s', Parse.parseImport start s = .ok d' s' ∧ d'.erase = (Decl.«import» sp names source).erase ∧
        Leaves s s' rest := by
  intro s ts rest hs hl ht hn hr
  obtain ⟨ik, ts₁, rfl, hik, h₁⟩ := Touching.cons_one (by simpa [keywordWord] using ht)
  obtain ⟨its, ts₂, rfl, hits, h₂⟩ := Touching.append_split h₁
  obtain ⟨lb, nts, rb, rfl, hlb, hnts, hrb⟩ := Touching.enclosed (by simpa [enclose] using hits)
  obtain ⟨fr, ts₃, rfl, hfr, h₃⟩ := Touching.cons_one (by simpa [identWord] using h₂)
  obtain ⟨st, ts₄, rfl, hst, h₄⟩ := Touching.cons_one h₃
  obtain ⟨semi, ts₅, rfl, hsemi, h₅⟩ := Touching.cons_one (by simpa [punctWord] using h₄)
  simp [Touching] at h₅; subst h₅
  have hs' : s.rest = ik :: lb :: (nts ++ rb :: fr :: st :: semi :: rest) := by simpa using hs
  let s₁ := advanced s ik lb (nts ++ rb :: fr :: st :: semi :: rest)
  let s₂ : ParseState := { s₁ with rest := nts ++ rb :: fr :: st :: semi :: rest, left := s₁.left - 1, lastStop := lb.span.stop }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁, hl, hs']
  have hlen := length_items hnts
  obtain ⟨res, s₃, hit, he, hL₃⟩ := import_loop names (10 * (s₂.left + 1)) #[] s₂ nts (fr :: st :: semi :: rest) rb
    hnames (by have h4 : s₂.left = nts.length + rest.length + 4 := (by simp [s₂, s₁, hl, hs']; omega); omega)
    rfl hrb hl₂ hnts
  have hs₃ : s₃.rest = rb :: fr :: st :: semi :: rest := hL₃.rest_eq
  let s₄ : ParseState := { s₃ with rest := fr :: st :: semi :: rest, left := s₃.left - 1, lastStop := rb.span.stop }
  let s₅ := advanced s₄ fr st (semi :: rest)
  let s₆ := advanced s₅ st semi rest
  have hres : res.isEmpty = false := by
    cases hres : res.toList with
    | nil => rw [hres] at he; cases names with
      | nil => exact absurd rfl hne
      | cons _ _ => simp at he
    | cons _ _ => simp [Array.isEmpty_iff, ← Array.toList_eq_nil_iff, hres]
  refine ⟨.«import» ⟨start, semi.span.stop⟩ res.toList source,
    { s₆ with rest := rest, left := s₆.left - 1, lastStop := semi.span.stop }, ?_, ?_, ?_⟩
  · simp only [Parse.parseImport]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl),
      Parse.bind_eq (Parse.peekAt_rest _ _)]
    rw [if_neg (show ¬ ((lb.isIdent "type" && _) = true) by simp [Token.isIdent, hlb]), Parse.pure_bind]
    rw [Parse.bind_eq (Parse.peek_eq (s := s₁) rfl), if_pos (show lb.isPunct "{" = true by simp [Token.isPunct, hlb]),
      Parse.pure_bind]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₁) rfl (by simp))), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_eq hit, Parse.bind_eq (Parse.expectPunct_ok hs₃ (by simp) hrb)]
    rw [if_neg (show ¬ (res.isEmpty = true) by simp [hres]), Parse.pure_bind,
      Parse.bind_eq (Parse.peek_eq (s := s₄) rfl), if_pos (show fr.isIdent "from" = true by simp [Token.isIdent, hfr]),
      Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₄) rfl)),
      Parse.bind_eq (Parse.advance_eq (s := s₅) rfl)]
    simp only [hst]
    rw [Parse.bind_eq (endStatement_semi (s := s₆) rfl hr hsemi), Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · simp [Decl.erase, ImportName.erase] at he ⊢
    exact he
  · exact leaves_trans (leaves_advanced hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans hL₃ (leaves_trans (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃]))
        (leaves_trans (leaves_advanced (s := s₄) rfl (by simp [s₄, hL₃.left_eq, hs₃]))
          (leaves_trans (leaves_advanced (s := s₅) rfl (by simp [s₅, s₄, hL₃.left_eq, hs₃]))
            (leaves_advance (s := s₆) rfl (by simp [s₆, s₅, s₄, hL₃.left_eq, hs₃])))))))

end tolean.TypeScript.Syntax
