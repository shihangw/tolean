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

end tolean.TypeScript.Syntax
