import tolean.TypeScript.Syntax.RoundTripStmt

/-!
The parser's round trip for declarations and modules, on tokens: the parser
reads the tokens that `Syntax/Source.lean` prints for a declaration as the
same declaration, apart from spans.

A declaration parses its parts with the fuel that `budget` gives. A statement
nests no deeper than it has tokens (`Stmt.depth_lt`), so that fuel is enough
for a statement or a block (`parseStatement_budget`, `parseBlock_budget`).

`parseDecl_reads` covers each kind of declaration that `Decl.wf` accepts. A
statement at the top of a module starts with no `import`, `export` or
`function`, and no name follows `interface` or `type` at its start on the same
line (`Stmt.declStart`), so `parseDecl` hands it to `parseStatement`.
`module_reads` proves the round trip for a module: `parseModule` reads the
tokens of the printed lines of every well-formed module, which the end of the
file follows, as that module apart from spans.
-/
namespace tolean.TypeScript.Syntax

open tolean

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
  | .funDecl sp n tps ps rt b => by
    have := Stmt.depth_lt b
    rw [Stmt.tokens_length_cons (l := keywordWord "function" :: identWord n :: typeParamWords tps ++
      enclose "(" ")" (ps.map Param.words) ++ typeAnnotation rt) (ls := b.wordLines)
      (by simp [Stmt.wordLines, Stmt.lines]), Stmt.tokens_eq]
    simp only [Stmt.depth]
    have : 1 ≤ (keywordWord "function" :: identWord n :: typeParamWords tps ++
      enclose "(" ")" (ps.map Param.words) ++ typeAnnotation rt).flatten.length := by simp [keywordWord]
    omega
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
  | .forOfPattern sp k p it b => by
    have := Stmt.depth_lt b
    rw [Stmt.tokens_length_cons (l := keywordWord "for" :: punctWord "(" :: k.word :: p.words ++ identWord "of" ::
      it.words ++ [punctWord ")"]) (ls := b.wordLines)
      (by simp [Stmt.wordLines, Stmt.lines, Stmt.lines_words b 1]), Stmt.tokens_eq]
    simp only [Stmt.depth]
    have : 1 ≤ (keywordWord "for" :: punctWord "(" :: k.word :: p.words ++ identWord "of" ::
      it.words ++ [punctWord ")"]).flatten.length := by simp [keywordWord]
    omega
  | .forStmt sp i t u b => by
    have := Stmt.depth_lt b
    rw [Stmt.tokens_length_cons (l := keywordWord "for" :: punctWord "(" :: forInitWords i ++ optWords t ++
      punctWord ";" :: optWords u ++ [punctWord ")"]) (ls := b.wordLines)
      (by simp [Stmt.wordLines, Stmt.lines, Stmt.lines_words b 1]), Stmt.tokens_eq]
    simp only [Stmt.depth]
    have : 1 ≤ (keywordWord "for" :: punctWord "(" :: forInitWords i ++ optWords t ++
      punctWord ";" :: optWords u ++ [punctWord ")"]).flatten.length := by simp [keywordWord]
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
  | .destructure _ k p t e => by
    simp [Stmt.depth, Stmt.tokens, Stmt.wordLines, Stmt.lines, destructureWords, VarKind.word_eq]
  | .exprStmt _ e => by simp [Stmt.depth, Stmt.tokens, Stmt.wordLines, Stmt.lines, punctWord]
  | .returnStmt _ v => by cases v <;> simp [Stmt.depth, Stmt.tokens, Stmt.wordLines, Stmt.lines, keywordWord]
  | .throwStmt _ e => by simp [Stmt.depth, Stmt.tokens, Stmt.wordLines, Stmt.lines, keywordWord]
  | .breakStmt _ | .continueStmt _ => by simp [Stmt.depth, Stmt.tokens, Stmt.wordLines, Stmt.lines, keywordWord]
  | .empty _ => by simp [Stmt.depth, Stmt.tokens, Stmt.wordLines, Stmt.lines, punctWord]
  | .switchStmt sp d cs => by
    have := Stmt.depthClauses_le cs
    rw [Stmt.tokens_length_cons (l := keywordWord "switch" :: punctWord "(" :: d.words ++
      [punctWord ")", punctWord "{"]) (ls := (cs.map clauseWordLines).flatten ++ [[punctWord "}"]])
      (by simp [Stmt.wordLines, Stmt.lines, Stmt.clauseLines_wordLines])]
    simp only [Stmt.depth, List.flatten_append, List.length_append, punctWord, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.length_cons, List.length_nil]
    omega

theorem Stmt.depthOf_le : ∀ ss : List Stmt, Stmt.depthOf ss ≤ (ss.map Stmt.tokens).flatten.length
  | [] => by simp [Stmt.depthOf]
  | st :: ss => by
    have := Stmt.depth_lt st; have := Stmt.depthOf_le ss
    simp only [Stmt.depthOf, List.map_cons, List.flatten_cons, List.length_append]
    omega

theorem Stmt.depthClauses_le : ∀ cs : List (Option Expr × List Stmt),
    Stmt.depthClauses cs ≤ (cs.map clauseWordLines).flatten.flatten.flatten.length
  | [] => by simp [Stmt.depthClauses]
  | (t, b) :: cs => by
    have h1 := Stmt.depthOf_le b; have := Stmt.depthClauses_le cs
    rw [← Stmt.tokensOf] at h1
    simp only [Stmt.depthClauses, List.map_cons, List.flatten_cons, clauseWordLines, List.flatten_append,
      List.length_append]
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

/-- `function`, a name, type parameters or none, `( params )`, a return type or
none, and a block, which `parseBlock` reads in a function. -/
theorem parseFunction_reads {T : Edition} (start : Pos) (exported : Bool) (sp : Span) (name : String)
    (typeParams : List String) (params : List Param) (rt : Option TypeExpr) (bsp : Span) (bs : List Stmt)
    (hname : exprName name = true) (htps : ∀ n ∈ typeParams, typeName n = true)
    (hps : ∀ p ∈ params, p.wf = true) (hrt : ∀ t ∈ rt, t.wf = true)
    (hbw : (Stmt.block bsp bs).wf T true false = true) :
    ∀ (s : ParseState) (ts bts rest : List Token), s.target = T → s.inFunction = false →
      s.rest = ts ++ bts ++ rest → s.left = s.rest.length →
      Touching ts (keywordWord "function" :: identWord name :: typeParamWords typeParams ++
        enclose "(" ")" (params.map Param.words) ++ typeAnnotation rt) →
      (∀ y ∈ ts.tail, NoBreak y) → Laid bts (Stmt.block bsp bs).wordLines → rest ≠ [] →
      ∃ d' s', Parse.parseFunction start exported s = .ok d' s' ∧
        d'.erase = (Decl.function sp exported name typeParams params rt (.block bsp bs)).erase ∧
        Leaves s s' rest := by
  intro s ts bts rest hT _ hs hl ht hn hb hr
  have hb' := hb
  simp only [Stmt.wordLines, Stmt.lines] at hb'
  obtain ⟨ba, bb, rfl, hba, _⟩ := Laid.cons hb'
  obtain ⟨lb, ba', rfl, hlb, _⟩ := Touching.cons_one (by simpa [punctWord] using hba)
  obtain ⟨ps', rt', s₁, hsig, hes, het, hL₁⟩ := parseSignature_reads name typeParams params rt hname htps hps hrt
    s ts lb (ba' ++ bb ++ rest) hT (by simpa using hs) hl ht hn hlb
  let s₂ : ParseState := { s₁ with inFunction := true, loopDepth := 0 }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, hL₁.left_eq, hL₁.rest_eq]
  obtain ⟨body', s₃, hpb, heb, hL₃⟩ := parseBlock_budget (loop := false) bsp bs hbw s₂ (lb :: ba' ++ bb) rest
    (by simp [s₂, hL₁.target_eq, hT]) rfl (fun h => by cases h) (by simp [s₂, hL₁.rest_eq]) hl₂ hb hr
  refine ⟨.function ⟨start, s₃.lastStop⟩ exported name typeParams ps' rt' body',
    { s₃ with inFunction := s₁.inFunction, loopDepth := s₁.loopDepth }, ?_, ?_,
    leaves_trans hL₁ (leaves_inFunctionBody hL₃)⟩
  · simp only [Parse.parseFunction]
    rw [Parse.bind_eq hsig, Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq (Parse.inFunctionBody_ok hpb),
      Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · simp [Decl.erase, hes, het, heb]

/-! ### Type aliases -/

/-- `type`, a name, type parameters or none, `=`, a type and `;`. -/
theorem parseTypeAlias_reads (start : Pos) (exported : Bool) (sp : Span) (name : String) (tps : List String)
    (ty : TypeExpr) (hname : exprName name = true) (htps : ∀ n ∈ tps, typeName n = true) (hty : ty.wf = true) :
    ∀ (s : ParseState) (ts rest : List Token), s.rest = ts ++ rest → s.left = s.rest.length →
      Touching ts (identWord "type" :: identWord name :: typeParamWords tps ++ punctWord "=" :: ty.words ++
        [punctWord ";"]) →
      (∀ y ∈ ts.tail, NoBreak y) → rest ≠ [] →
      ∃ d' s', Parse.parseTypeAlias start exported s = .ok d' s' ∧
        d'.erase = (Decl.typeAlias sp exported name tps ty).erase ∧ Leaves s s' rest := by
  intro s ts rest hs hl ht hn hr
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  obtain ⟨tk, ts₁, rfl, htk, h₁⟩ := Touching.cons_one (by simpa [identWord] using ht)
  obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  obtain ⟨gts, ts₂', rfl, hgts, h₂'⟩ := Touching.append_split h₂
  obtain ⟨eq, ts₃, rfl, heq, h₃⟩ := Touching.cons_one (by simpa [punctWord] using h₂')
  obtain ⟨tts, ts₄, rfl, htt, h₄⟩ := Touching.append_split h₃
  obtain ⟨semi, ts₅, rfl, hsemi, h₅⟩ := Touching.cons_one (by simpa [punctWord] using h₄)
  simp [Touching] at h₅; subst h₅
  have hs' : s.rest = tk :: nm :: (gts ++ eq :: (tts ++ semi :: rest)) := by simpa using hs
  let s₁ := past s tk (nm :: (gts ++ eq :: (tts ++ semi :: rest)))
  let s₂ := past s₁ nm (gts ++ eq :: (tts ++ semi :: rest))
  obtain ⟨s₂', hgp, hLg⟩ := parseTypeParams_reads tps htps s₂ gts (eq :: (tts ++ semi :: rest)) rfl
    (by simp [s₂, s₁, hl, hs']) hgts ⟨eq, _, rfl, by rw [heq]; exact punct_ne (by decide)⟩
  have hs₂' : s₂'.rest = eq :: (tts ++ semi :: rest) := hLg.rest_eq
  have hrn : Parse.readName s₁ = .ok name s₂ := by
    obtain ⟨u, r', hur⟩ := List.exists_cons_of_ne_nil (show gts ++ eq :: (tts ++ semi :: rest) ≠ [] by simp)
    show Parse.readName s₁ = .ok name (past s₁ nm _)
    rw [hur]; exact readName_ok (by simp only [s₁]; rw [hur]) hnm hname'
  let s₃ : ParseState := { s₂' with rest := tts ++ semi :: rest, left := s₂'.left - 1, lastStop := eq.span.stop }
  have hl₃ : s₃.left = s₃.rest.length := by simp only [s₃]; rw [hLg.left_eq]; simp
  obtain ⟨t', s₄, hpt, het, hL₄⟩ := parseType_budget ty hty s₃ tts (semi :: rest) rfl hl₃ htt.kinds
    (fun y hy => hn y (by simp [hy])) (by simp) (followsType_eq_semi (.inr hsemi))
  have hs₄ : s₄.rest = semi :: rest := hL₄.rest_eq
  refine ⟨.typeAlias ⟨start, semi.span.stop⟩ exported name tps t',
    { s₄ with rest := rest, left := s₄.left - 1, lastStop := semi.span.stop }, ?_, by simp [Decl.erase, het],
    leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans hLg (leaves_trans (leaves_advance hs₂' (by rw [hLg.left_eq, hs₂'])) (leaves_trans hL₄
        (leaves_advance hs₄ (by rw [hL₄.left_eq, hs₄]))))))⟩
  simp only [Parse.parseTypeAlias]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq hrn, Parse.bind_eq hgp]
  rw [Parse.bind_eq (Parse.expectPunct_ok hs₂' (by simp) heq), Parse.bind_eq (Parse.budget_eq _),
    Parse.bind_eq hpt, Parse.bind_eq (endStatement_semi hs₄ hr hsemi), Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl

/-! ### The second token of an expression -/

/-- A token kind that is not a name. -/
def NotIdent (k : TokenKind) : Prop := ∀ m, k ≠ .ident m

/-- The second token of `a ++ b` is the second of `a`, or the first of `b`. -/
theorem second_append {a b : List TokenKind} {k₀ : TokenKind} {bs : List TokenKind} {n : String}
    (hb : b = k₀ :: bs) (hk₀ : NotIdent k₀) (ha : a ≠ [])
    (IH : ∀ {k r}, a = .ident n :: k :: r → NotIdent k) :
    ∀ {k r}, a ++ b = .ident n :: k :: r → NotIdent k := by
  intro k r h
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
  cases op <;> simp [AssignOp.symbol, symbol, Lex.reservedWords, punctWord, NotIdent]

/-- No `as` or `satisfies` follows one of `Parse.declarationWords` at the left
edge of `e`, where it would make a name the second token of `e`. -/
def Expr.spineOK : Expr → Bool
  | .member _ o _ | .optMember _ o _ | .index _ o _ | .call _ o _ | .postfix _ _ o | .binary _ _ o _
  | .cond _ o _ _ | .assign _ _ o _ => o.spineOK
  | .asConst _ o | .satisfies _ o _ => !Parse.refusedBeforeType o && o.spineOK
  | _ => true

/-- An expression whose only token is a name is that name. -/
theorem Expr.eq_ident_of_tokens : ∀ (e : Expr) {n : String}, e.tokens = [.ident n] → ∃ sp, e = .ident sp n
  | .ident sp m, _, h => ⟨sp, by simp [Expr.tokens, Expr.words, identWord] at h; rw [h]⟩
  | .number .., _, h | .bigint .., _, h | .string .., _, h | .null _, _, h => by
    simp [Expr.tokens, Expr.words, keywordWord] at h
  | .bool _ b, _, h => by cases b <;> simp [Expr.tokens, Expr.words, keywordWord] at h
  | .array .., _, h => by simp [Expr.tokens_array] at h
  | .object .., _, h => by simp [Expr.tokens_object] at h
  | .paren .., _, h => by simp [Expr.tokens_paren] at h
  | .prefix _ op _, _, h => by cases op <;> simp [Expr.tokens_prefix, UpdateOp.symbol] at h
  | .unary _ op a, _, h => by
    have := congrArg List.length h
    have ha := List.length_pos_iff.mpr (Expr.tokens_ne_nil a)
    rw [Expr.tokens_unary] at this
    cases op <;> simp [UnaryOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord] at this <;>
      first | omega | exact absurd this (Expr.tokens_ne_nil a)
  | .member _ o _, _, h | .optMember _ o _, _, h | .postfix _ _ o, _, h => by
    have := congrArg List.length h
    have ho := List.length_pos_iff.mpr (Expr.tokens_ne_nil o)
    first
      | (rw [Expr.tokens_member] at this; simp at this <;> first | omega | exact absurd this (Expr.tokens_ne_nil o))
      | (rw [Expr.tokens_optMember] at this; simp at this <;> first | omega | exact absurd this (Expr.tokens_ne_nil o))
      | (rw [Expr.tokens_postfix] at this; simp at this <;> first | omega | exact absurd this (Expr.tokens_ne_nil o))
  | .index _ o _, _, h | .call _ o _, _, h | .asConst _ o, _, h | .satisfies _ o _, _, h => by
    have := congrArg List.length h
    have ho := List.length_pos_iff.mpr (Expr.tokens_ne_nil o)
    first
      | (rw [Expr.tokens_index] at this; simp at this <;> first | omega | exact absurd this (Expr.tokens_ne_nil o))
      | (rw [Expr.tokens_call] at this; simp at this <;> first | omega | exact absurd this (Expr.tokens_ne_nil o))
      | (rw [Expr.tokens_asConst] at this; simp at this <;> first | omega | exact absurd this (Expr.tokens_ne_nil o))
      | (rw [Expr.tokens_satisfies] at this; simp at this <;> first | omega | exact absurd this (Expr.tokens_ne_nil o))
  | .binary _ op o _, _, h | .assign _ op o _, _, h => by
    have := congrArg List.length h
    have ho := List.length_pos_iff.mpr (Expr.tokens_ne_nil o)
    first
      | (rw [Expr.tokens_binary] at this; obtain ⟨k, ks, hk, _⟩ := binOp_head op; simp [hk] at this
         first | omega | exact absurd this.1 (Expr.tokens_ne_nil o) | exact absurd this (Expr.tokens_ne_nil o))
      | (rw [Expr.tokens_assign] at this; obtain ⟨k, ks, hk, _⟩ := assignOp_head op; simp [hk] at this
         first | omega | exact absurd this.1 (Expr.tokens_ne_nil o) | exact absurd this (Expr.tokens_ne_nil o))
  | .cond _ o _ _, _, h => by
    have := congrArg List.length h
    have ho := List.length_pos_iff.mpr (Expr.tokens_ne_nil o)
    rw [Expr.tokens_cond] at this; simp at this
    first | omega | exact absurd this.1 (Expr.tokens_ne_nil o) | exact absurd this (Expr.tokens_ne_nil o)
  | .arrow _ parens ps _, _, h => by
    rw [Expr.tokens_arrow] at h
    rcases arrowParams_cases parens ps with ⟨p, _, _, hp⟩ | hp
    · simp [hp, identWord] at h
    · simp [hp, enclose, punctWord] at h

/-- The second token of `l ++ x :: b`, where `x` is `as` or `satisfies`, when
`l` is no name that the parser refuses before them. -/
theorem second_typeOp (l : Expr) {x : TokenKind} {b : List TokenKind} {n : String}
    (hl : Parse.refusedBeforeType l = false) (ih : ∀ {k r}, l.tokens = .ident n :: k :: r → NotIdent k)
    {k : TokenKind} {r : List TokenKind}
    (hn : n ∈ Parse.declarationWords) (h : l.tokens ++ x :: b = .ident n :: k :: r) : NotIdent k := by
  cases hlt : l.tokens with
  | nil => exact absurd hlt (Expr.tokens_ne_nil l)
  | cons y ys =>
    rw [hlt] at h
    cases ys with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      obtain ⟨sp, rfl⟩ := Expr.eq_ident_of_tokens l hlt
      simp [Parse.refusedBeforeType, hn] at hl
    | cons z zs =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ih hlt

/-- An expression that starts with one of `Parse.declarationWords` has no
name as its second token: an operator, a `.`, a `(` or a `[` follows the
name, if anything does. The parser refuses `as` and `satisfies` after such a
name, and `spineOK` states it. -/
theorem Expr.second : ∀ (e : Expr) {n : String} {k : TokenKind} {r : List TokenKind},
    e.spineOK = true → n ∈ Parse.declarationWords → e.tokens = .ident n :: k :: r → NotIdent k
  | .member sp o p, _, _, _, hs, hn, h => by
    rw [Expr.tokens_member] at h
    exact second_append rfl (by simp [NotIdent]) (Expr.tokens_ne_nil o) (fun h' => Expr.second o (by simpa [Expr.spineOK] using hs) hn h') h
  | .optMember sp o p, _, _, _, hs, hn, h => by
    rw [Expr.tokens_optMember] at h
    exact second_append rfl (by simp [NotIdent]) (Expr.tokens_ne_nil o) (fun h' => Expr.second o (by simpa [Expr.spineOK] using hs) hn h') h
  | .index sp o i, _, _, _, hs, hn, h => by
    rw [Expr.tokens_index, List.append_assoc] at h
    exact second_append rfl (by simp [NotIdent]) (Expr.tokens_ne_nil o) (fun h' => Expr.second o (by simpa [Expr.spineOK] using hs) hn h') h
  | .call sp c as, _, _, _, hs, hn, h => by
    rw [Expr.tokens_call, List.append_assoc] at h
    exact second_append rfl (by simp [NotIdent]) (Expr.tokens_ne_nil c) (fun h' => Expr.second c (by simpa [Expr.spineOK] using hs) hn h') h
  | .postfix sp op a, _, _, _, hs, hn, h => by
    rw [Expr.tokens_postfix] at h
    exact second_append rfl (by simp [NotIdent]) (Expr.tokens_ne_nil a) (fun h' => Expr.second a (by simpa [Expr.spineOK] using hs) hn h') h
  | .binary sp op l r', _, _, _, hs, hn, h => by
    rw [Expr.tokens_binary, List.append_assoc] at h
    obtain ⟨k₀, ks, hk, hn₀⟩ := notIdent_binOp op
    exact second_append (by rw [hk]; rfl) hn₀ (Expr.tokens_ne_nil l) (fun h' => Expr.second l (by simpa [Expr.spineOK] using hs) hn h') h
  | .cond sp t a b, _, _, _, hs, hn, h => by
    rw [Expr.tokens_cond, List.append_assoc] at h
    exact second_append rfl (by simp [NotIdent]) (Expr.tokens_ne_nil t) (fun h' => Expr.second t (by simpa [Expr.spineOK] using hs) hn h') h
  | .assign sp op t v, _, _, _, hs, hn, h => by
    rw [Expr.tokens_assign, List.append_assoc] at h
    obtain ⟨k₀, ks, hk, hn₀⟩ := notIdent_assignOp op
    exact second_append (by rw [hk]; rfl) hn₀ (Expr.tokens_ne_nil t) (fun h' => Expr.second t (by simpa [Expr.spineOK] using hs) hn h') h
  | .asConst sp l, n, k, r, hs, hn, h => by
    simp only [Expr.spineOK, Bool.and_eq_true, Bool.not_eq_true'] at hs
    rw [Expr.tokens_asConst] at h
    exact second_typeOp l hs.1 (fun h' => Expr.second l hs.2 hn h') hn h
  | .satisfies sp l t, n, k, r, hs, hn, h => by
    simp only [Expr.spineOK, Bool.and_eq_true, Bool.not_eq_true'] at hs
    rw [Expr.tokens_satisfies] at h
    exact second_typeOp l hs.1 (fun h' => Expr.second l hs.2 hn h') hn h
  | .ident .., _, _, _, _, _, h | .number .., _, _, _, _, _, h | .bigint .., _, _, _, _, _, h | .string .., _, _, _, _, _, h
  | .null _, _, _, _, _, _, h => by simp [Expr.tokens, Expr.words, identWord, keywordWord] at h
  | .bool _ b, _, _, _, _, _, h => by cases b <;> simp [Expr.tokens, Expr.words, keywordWord] at h
  | .array .., _, _, _, _, _, h => by simp [Expr.tokens_array] at h
  | .object .., _, _, _, _, _, h => by simp [Expr.tokens_object] at h
  | .paren .., _, _, _, _, _, h => by simp [Expr.tokens_paren] at h
  | .unary _ op _, _, _, _, _, _, h => by
    rw [Expr.tokens_unary] at h
    cases op <;> simp [UnaryOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord] at h
  | .prefix .., _, _, _, _, _, h => by simp [Expr.tokens_prefix] at h
  | .arrow _ parens ps _, _, _, _, _, _, h => by
    rw [Expr.tokens_arrow] at h
    rcases arrowParams_cases parens ps with ⟨p, _, _, hp⟩ | hp
    · simp [hp, identWord] at h; rw [← h.2.1]; simp [NotIdent]
    · simp [hp, enclose, punctWord] at h


/-- Every well-formed expression is `spineOK`. -/
theorem Expr.spineOK_wf {T : Edition} : ∀ (e : Expr) (level : Level), e.wfAt T level = true → e.spineOK = true
  | .spread .., level, h => by cases level <;> simp [Expr.wfAt] at h
  | .member _ o _, level, h | .index _ o _, level, h | .call _ o _, level, h => by
    have : o.wfAt T .lhs = true := by cases level <;> simp_all [Expr.wfAt]
    simpa [Expr.spineOK] using Expr.spineOK_wf o .lhs this
  | .optMember _ o _, level, h => by
    have : o.wfAt T .lhs = true := by cases level <;> simp_all [Expr.wfAt]
    simpa [Expr.spineOK] using Expr.spineOK_wf o .lhs this
  | .postfix _ _ o, level, h => by
    have : o.wfAt T .lhs = true := by cases level <;> simp_all [Expr.wfAt]
    simpa [Expr.spineOK] using Expr.spineOK_wf o .lhs this
  | .binary _ _ o _, level, h => by
    have : ∃ m, o.wfAt T (.bin m) = true := by
      cases level with
      | assign => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨0, h.1.1.1.1.2⟩
      | cond => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨0, h.1.1.1.1.2⟩
      | bin m => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨m, h.1.1.1.1.2⟩
      | _ => simp [Expr.wfAt] at h
    obtain ⟨m, hm⟩ := this
    simpa [Expr.spineOK] using Expr.spineOK_wf o (.bin m) hm
  | .asConst _ o, level, h => by
    have : ∃ m, o.wfAt T (.bin m) = true ∧ leftOKType o = true := by
      cases level with
      | assign => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨0, h.1.2, h.2⟩
      | cond => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨0, h.1.2, h.2⟩
      | bin m => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨m, h.1.2, h.2⟩
      | _ => simp [Expr.wfAt] at h
    obtain ⟨m, hm, hlo⟩ := this
    simp [Expr.spineOK, leftOKType_refused hlo, Expr.spineOK_wf o (.bin m) hm]
  | .satisfies _ o _, level, h => by
    have : ∃ m, o.wfAt T (.bin m) = true ∧ leftOKType o = true := by
      cases level with
      | assign => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨0, h.1.1.2, h.1.2⟩
      | cond => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨0, h.1.1.2, h.1.2⟩
      | bin m => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨m, h.1.1.2, h.1.2⟩
      | _ => simp [Expr.wfAt] at h
    obtain ⟨m, hm, hlo⟩ := this
    simp [Expr.spineOK, leftOKType_refused hlo, Expr.spineOK_wf o (.bin m) hm]
  | .cond _ o _ _, level, h => by
    have : o.wfAt T (.bin 0) = true := by
      cases level with
      | assign => simp [Expr.wfAt] at h; exact h.1.1.1
      | cond => simp [Expr.wfAt] at h; exact h.1.1.1
      | _ => simp [Expr.wfAt] at h
    simpa [Expr.spineOK] using Expr.spineOK_wf o (.bin 0) this
  | .assign _ _ o _, level, h => by
    have : o.wfAt T .cond = true := by
      cases level with
      | assign => simp [Expr.wfAt] at h; exact h.1.1.1
      | _ => simp [Expr.wfAt] at h
    simpa [Expr.spineOK] using Expr.spineOK_wf o .cond this
  | .ident .., _, _ | .number .., _, _ | .bigint .., _, _ | .string .., _, _ | .bool .., _, _ | .null _, _, _
  | .array .., _, _ | .object .., _, _ | .paren .., _, _ | .unary .., _, _ | .prefix .., _, _
  | .arrow .., _, _ | .new .., _, _ => by simp [Expr.spineOK]

/-! ### Fields of an interface -/

/-- `name: T;`, without `readonly` and `?`. -/
theorem parseField_plain (sp : Span) (name : String) (ty : TypeExpr) (hty : ty.wf = true)
    (s : ParseState) (ts rest : List Token) (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length)
    (ht : Touching ts (Field.words ⟨sp, false, name, false, ty⟩)) (hn : ∀ y ∈ ts.tail, NoBreak y)
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
  let s₁ := past s nm (c :: (tts ++ semi :: rest))
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
    leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans hL₃ (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃]))))⟩
  simp only [Parse.parseField]
  rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.peekAt_rest _ _)]
  simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent, hc,
    Bool.and_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind]
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
    (ht : Touching ts (Field.words ⟨sp, false, name, true, ty⟩)) (hn : ∀ y ∈ ts.tail, NoBreak y)
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
  let s₁ := past s nm (q :: (c :: (tts ++ semi :: rest)))
  let s₁' := past s₁ q (c :: (tts ++ semi :: rest))
  let s₂ : ParseState := { s₁' with rest := tts ++ semi :: rest, left := s₁'.left - 1, lastStop := c.span.stop }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁', s₁, hl, hs']
  obtain ⟨t', s₃, hpt, het, hL₃⟩ := parseType_budget ty hty s₂ tts (semi :: rest) rfl hl₂ htt.kinds
    (fun y hy => hn y (by simp [hy])) (by simp) (followsType_eq_semi (.inr hsemi))
  have hs₃ : s₃.rest = semi :: rest := hL₃.rest_eq
  refine ⟨⟨⟨nm.span.start, semi.span.stop⟩, false, name, true, t'⟩,
    { s₃ with rest := rest, left := s₃.left - 1, lastStop := semi.span.stop }, ?_, by simp [Field.erase, het],
    leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₁') rfl (by simp [s₁', s₁, hl, hs']))
        (leaves_trans hL₃ (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃])))))⟩
  simp only [Parse.parseField]
  rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.peekAt_rest _ _)]
  simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent, hq,
    Bool.and_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind]
  rw [Parse.bind_eq (readPropertyName_ok hs' hnm), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
  rw [if_pos (show q.isPunct "?" = true by simp [Token.isPunct, hq]),
    Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₁) rfl)), Parse.bind_eq (Parse.peek_eq (s := s₁') rfl)]
  rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hc] at h)]
  rw [if_pos (show c.isPunct ":" = true by simp [Token.isPunct, hc]), Parse.pure_bind]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₁') rfl (by simp))), Parse.bind_eq (Parse.budget_eq _),
    Parse.bind_eq hpt, Parse.bind_eq (Parse.peek_eq hs₃)]
  rw [if_pos (show (semi.isPunct ";" || semi.isPunct ",") = true by simp [Token.isPunct, hsemi])]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs₃ hr)), Parse.bind_eq (Parse.spanFrom_eq _ _)]
  simp [Token.isPunct, hq, pure, EStateM.pure]

/-- `readonly name: T;` or `readonly name?: T;`. -/
theorem parseField_ro (sp : Span) (name : String) (opt : Bool) (ty : TypeExpr) (hty : ty.wf = true)
    (s : ParseState) (ts rest : List Token) (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length)
    (ht : Touching ts (Field.words ⟨sp, true, name, opt, ty⟩)) (hn : ∀ y ∈ ts.tail, NoBreak y)
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
  have hnmn : nm.newlineBefore = false := hn nm (by simp) (by rcases hnmk with h | h <;> simp [h])
  cases opt with
  | false =>
    obtain ⟨c, ts₂, rfl, hc, h₂⟩ := Touching.cons_one (by simpa [punctWord] using h₁)
    obtain ⟨tts, ts₃, rfl, htt, h₃⟩ := Touching.append_split h₂
    obtain ⟨semi, ts₄, rfl, hsemi, h₄⟩ := Touching.cons_one (by simpa [punctWord] using h₃)
    simp [Touching] at h₄; subst h₄
    have hs' : s.rest = ro :: nm :: c :: (tts ++ semi :: rest) := by simpa using hs
    let s₀ := past s ro (nm :: (c :: (tts ++ semi :: rest)))
    let s₁ := past s₀ nm (c :: (tts ++ semi :: rest))
    let s₂ : ParseState := { s₁ with rest := tts ++ semi :: rest, left := s₁.left - 1, lastStop := c.span.stop }
    have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁, s₀, hl, hs']
    obtain ⟨t', s₃, hpt, het, hL₃⟩ := parseType_budget ty hty s₂ tts (semi :: rest) rfl hl₂ htt.kinds
      (fun y hy => hn y (by simp [hy])) (by simp) (followsType_eq_semi (.inr hsemi))
    have hs₃ : s₃.rest = semi :: rest := hL₃.rest_eq
    refine ⟨⟨⟨ro.span.start, semi.span.stop⟩, true, name, false, t'⟩,
      { s₃ with rest := rest, left := s₃.left - 1, lastStop := semi.span.stop }, ?_, by simp [Field.erase, het],
      leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₀) rfl (by simp [s₀, hl, hs']))
        (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, s₀, hl, hs']))
          (leaves_trans hL₃ (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃])))))⟩
    simp only [Parse.parseField]
    rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.peekAt_rest _ _)]
    rcases hnmk with hnmk | hnmk
    all_goals
      simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent, Token.isIdent,
        hro, hnmk, hnmn, beq_self_eq_true, Bool.not_false, Bool.true_or, Bool.or_true, Bool.and_true,
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
    let s₀ := past s ro (nm :: (q :: c :: (tts ++ semi :: rest)))
    let s₁ := past s₀ nm (q :: (c :: (tts ++ semi :: rest)))
    let s₁' := past s₁ q (c :: (tts ++ semi :: rest))
    let s₂ : ParseState := { s₁' with rest := tts ++ semi :: rest, left := s₁'.left - 1, lastStop := c.span.stop }
    have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁', s₁, s₀, hl, hs']
    obtain ⟨t', s₃, hpt, het, hL₃⟩ := parseType_budget ty hty s₂ tts (semi :: rest) rfl hl₂ htt.kinds
      (fun y hy => hn y (by simp [hy])) (by simp) (followsType_eq_semi (.inr hsemi))
    have hs₃ : s₃.rest = semi :: rest := hL₃.rest_eq
    refine ⟨⟨⟨ro.span.start, semi.span.stop⟩, true, name, true, t'⟩,
      { s₃ with rest := rest, left := s₃.left - 1, lastStop := semi.span.stop }, ?_, by simp [Field.erase, het],
      leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₀) rfl (by simp [s₀, hl, hs']))
        (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, s₀, hl, hs']))
          (leaves_trans (leaves_advance (s := s₁') rfl (by simp [s₁', s₁, s₀, hl, hs']))
            (leaves_trans hL₃ (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃]))))))⟩
    simp only [Parse.parseField]
    rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.peekAt_rest _ _)]
    rcases hnmk with hnmk | hnmk
    all_goals
      simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent, Token.isIdent,
        hro, hnmk, hnmn, beq_self_eq_true, Bool.not_false, Bool.true_or, Bool.or_true, Bool.and_true,
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
      simp [Token.isPunct, hq, pure, EStateM.pure]


/-- A field of an interface: `readonly` or not, a name, `?` or not, `:`, a type and `;`. -/
theorem parseField_reads (f : Field) (hty : f.type.wf = true) (s : ParseState) (ts rest : List Token)
    (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length) (ht : Touching ts f.words)
    (hn : ∀ y ∈ ts.tail, NoBreak y) (hr : rest ≠ []) :
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
  intro fields fuel acc s ts rest c hw hlen hs hc hl ht
  have hflat : ∀ l : List Field, (l.map fun f => [f.words]).flatten = l.map Field.words := by
    intro l; induction l with
    | nil => rfl
    | cons f l ih => simp [ih]
  refine blockStep_loop (lines := fun f => [f.words]) (Inv := fun _ => True) (fun _ _ => trivial) ?_ hc fields
    (fun y hy => hy) fuel acc s ts hlen trivial hs hl (by rw [hflat]; exact ht)
  intro f hf _ _ s a b _ hs hl ha _
  obtain ⟨ha', hna⟩ := Laid.one ha
  obtain ⟨k, hk, hk1, hk2⟩ := Field.first f
  obtain ⟨x, a', rfl, hx⟩ : ∃ x a', a = x :: a' ∧ x.kind = k := by
    have hk' : (a.map (·.kind)).head? = some k := by rw [ha'.kinds]; exact hk
    cases a with
    | nil => simp at hk'
    | cons x a' => simp at hk'; exact ⟨x, a', rfl, hk'⟩
  obtain ⟨f₁, s₁, hp, he, hL₁⟩ := parseField_reads f (hw f hf) s (x :: a') (b ++ c :: rest) hs hl ha' hna (by simp)
  exact ⟨f₁, s₁, x, a', rfl, by rw [hx]; exact hk1, by rw [hx]; exact hk2, hp, he, hL₁⟩

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


/-- `interface`, a name, type parameters or none, and `{`, the fields on their
own lines, and `}`. -/
theorem parseInterface_reads (start : Pos) (exported : Bool) (sp : Span) (name : String) (tps : List String)
    (fields : List Field) (hname : exprName name = true) (htps : ∀ n ∈ tps, typeName n = true)
    (hfs : ∀ f ∈ fields, f.type.wf = true) :
    ∀ (s : ParseState) (ts fts rest : List Token) (rb : Token), s.rest = ts ++ fts ++ rb :: rest →
      s.left = s.rest.length →
      Touching ts (identWord "interface" :: identWord name :: typeParamWords tps ++ [punctWord "{"]) →
      Laid fts (fields.map Field.words) → rb.kind = .punct "}" → rest ≠ [] →
      ∃ d' s', Parse.parseInterface start exported s = .ok d' s' ∧
        d'.erase = (Decl.interface sp exported name tps fields).erase ∧ Leaves s s' rest := by
  intro s ts fts rest rb hs hl ht hf hrb hr
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  obtain ⟨it, ts₁, rfl, hit, h₁⟩ := Touching.cons_one (by simpa [identWord] using ht)
  obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  obtain ⟨gts, ts₂', rfl, hgts, h₂'⟩ := Touching.append_split h₂
  obtain ⟨lb, ts₃, rfl, hlb, h₃⟩ := Touching.cons_one (by simpa [punctWord] using h₂')
  simp [Touching] at h₃; subst h₃
  have hs' : s.rest = it :: nm :: (gts ++ lb :: (fts ++ rb :: rest)) := by simpa using hs
  let s₁ := past s it (nm :: (gts ++ lb :: (fts ++ rb :: rest)))
  let s₂ := past s₁ nm (gts ++ lb :: (fts ++ rb :: rest))
  obtain ⟨s₂', hgp, hLg⟩ := parseTypeParams_reads tps htps s₂ gts (lb :: (fts ++ rb :: rest)) rfl
    (by simp [s₂, s₁, hl, hs']) hgts ⟨lb, _, rfl, by rw [hlb]; exact punct_ne (by decide)⟩
  have hs₂' : s₂'.rest = lb :: (fts ++ rb :: rest) := hLg.rest_eq
  have hrn : Parse.readName s₁ = .ok name s₂ := by
    obtain ⟨u, r', hur⟩ := List.exists_cons_of_ne_nil (show gts ++ lb :: (fts ++ rb :: rest) ≠ [] by simp)
    show Parse.readName s₁ = .ok name (past s₁ nm _)
    rw [hur]; exact readName_ok (by simp only [s₁]; rw [hur]) hnm hname'
  let s₃ : ParseState := { s₂' with rest := fts ++ rb :: rest, left := s₂'.left - 1, lastStop := lb.span.stop }
  have hl₃ : s₃.left = s₃.rest.length := by simp only [s₃]; rw [hLg.left_eq]; simp
  have hlen := Laid.length_fields hf
  obtain ⟨res, s₄, hit', he, hL₄⟩ := field_loop fields (10 * (s₃.left + 1)) #[] s₃ fts rest rb hfs
    (by have : s₃.left = fts.length + rest.length + 1 := by simp only [s₃]; rw [hLg.left_eq]; simp; omega
        omega) rfl hrb hl₃ hf
  have hs₄ : s₄.rest = rb :: rest := hL₄.rest_eq
  have hn2 : lb.kind ≠ .keyword "extends" := by rw [hlb]; simp
  refine ⟨.interface ⟨start, rb.span.stop⟩ exported name tps res.toList,
    { s₄ with rest := rest, left := s₄.left - 1, lastStop := rb.span.stop }, ?_, ?_,
    leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans hLg (leaves_trans (leaves_advance hs₂' (by rw [hLg.left_eq, hs₂'])) (leaves_trans hL₄
        (leaves_advance hs₄ (by rw [hL₄.left_eq, hs₄]))))))⟩
  · simp only [Parse.parseInterface]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq hrn, Parse.bind_eq hgp,
      Parse.bind_eq (Parse.peek_eq hs₂')]
    rw [Parse.ite_guard (fun h => by simp [Token.isKeyword, hn2] at h)]
    rw [Parse.bind_eq (Parse.expectPunct_ok hs₂' (by simp) hlb), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_eq hit', Parse.bind_eq (Parse.expectPunct_ok hs₄ hr hrb), Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · simp [Decl.erase] at he ⊢
    exact he

/-! ### Enums -/

/-- `Name = "value",`: a member of an enum, and the `,` after it. -/
theorem parseEnumMember_reads (m : EnumMember) (s : ParseState) (ts rest : List Token)
    (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length) (ht : Touching ts m.words)
    (hr : rest ≠ []) :
    ∃ m' s', Parse.parseEnumMember s = .ok m' s' ∧ m'.erase = m.erase ∧ Leaves s s' rest := by
  obtain ⟨sp, name, value⟩ := m
  simp only [EnumMember.words] at ht
  obtain ⟨nm, ts₁, rfl, hnm, h₁⟩ : ∃ nm ts₁, ts = nm :: ts₁ ∧ [nm.kind] = propertyName name ∧
      Touching ts₁ [punctWord "=", [.string value], punctWord ","] := by
    obtain ⟨a, b, rfl, ha, _, hb⟩ := ht
    have hlen := congrArg List.length ha
    rw [List.length_map, length_propertyName] at hlen
    match a, ha with
    | [nm], ha => exact ⟨nm, b, rfl, by simpa using ha, hb⟩
  obtain ⟨eq, ts₂, rfl, heq, h₂⟩ := Touching.cons_one (by simpa [punctWord] using h₁)
  obtain ⟨str, ts₃, rfl, hstr, h₃⟩ := Touching.cons_one h₂
  obtain ⟨comma, ts₄, rfl, hcomma, h₄⟩ := Touching.cons_one (by simpa [punctWord] using h₃)
  simp [Touching] at h₄; subst h₄
  have hs' : s.rest = nm :: eq :: str :: comma :: rest := by simpa using hs
  let s₁ := past s nm (eq :: str :: comma :: rest)
  let s₂ := past s₁ eq (str :: comma :: rest)
  let s₃ := past s₂ str (comma :: rest)
  refine ⟨⟨⟨nm.span.start, str.span.stop⟩, name, value⟩,
    { s₃ with rest := rest, left := s₃.left - 1, lastStop := comma.span.stop }, ?_, by simp [EnumMember.erase],
    leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs']))
        (leaves_advance (s := s₃) rfl (by simp [s₃, s₂, s₁, hl, hs']))))⟩
  simp only [Parse.parseEnumMember]
  rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (readPropertyName_ok hs' hnm),
    Parse.bind_eq (Parse.peek_eq (s := s₁) rfl)]
  rw [if_pos (show eq.isPunct "=" = true by simp [Token.isPunct, heq]), Parse.pure_bind]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₁) rfl)),
    Parse.bind_eq (Parse.advance_eq (s := s₂) rfl)]
  simp only [hstr]
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _), Parse.bind_eq (Parse.peek_eq (s := s₃) rfl)]
  rw [if_pos (show comma.isPunct "," = true by simp [Token.isPunct, hcomma])]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₃) rfl hr))]
  rfl

/-- A member starts with its name, so not with `}` and not at the end of the file. -/
theorem EnumMember.first (m : EnumMember) :
    ∃ k, m.words.flatten.head? = some k ∧ k ≠ .punct "}" ∧ k ≠ .eof := by
  by_cases h : m.name ∈ Lex.reservedWords
  · exact ⟨.keyword m.name, by simp [EnumMember.words, propertyName, h, keywordWord], by simp, by simp⟩
  · exact ⟨.ident m.name, by simp [EnumMember.words, propertyName, h, identWord], by simp, by simp⟩

/-- The loop of `parseEnum` reads the members of an enum, one on each line, which a `}` follows. -/
theorem enumMember_loop :
    ∀ (members : List EnumMember) (fuel : Nat) (acc : Array EnumMember) (s : ParseState)
      (ts rest : List Token) (c : Token),
      members.length < fuel → s.rest = ts ++ c :: rest → c.kind = .punct "}" → s.left = s.rest.length →
      Laid ts (members.map EnumMember.words) →
      ∃ res s', Parse.iterate fuel acc (Parse.blockStep Parse.parseEnumMember) s = .ok res s' ∧
        res.toList.map EnumMember.erase = (acc.toList ++ members).map EnumMember.erase ∧
        Leaves s s' (c :: rest) := by
  intro members fuel acc s ts rest c hlen hs hc hl ht
  have hflat : ∀ l : List EnumMember, (l.map fun m => [m.words]).flatten = l.map EnumMember.words := by
    intro l; induction l with
    | nil => rfl
    | cons m l ih => simp [ih]
  refine blockStep_loop (lines := fun m => [m.words]) (Inv := fun _ => True) (fun _ _ => trivial) ?_ hc members
    (fun y hy => hy) fuel acc s ts hlen trivial hs hl (by rw [hflat]; exact ht)
  intro m _ _ _ s a b _ hs hl ha _
  obtain ⟨ha', _⟩ := Laid.one ha
  obtain ⟨k, hk, hk1, hk2⟩ := EnumMember.first m
  obtain ⟨x, a', rfl, hx⟩ : ∃ x a', a = x :: a' ∧ x.kind = k := by
    have hk' : (a.map (·.kind)).head? = some k := by rw [ha'.kinds]; exact hk
    cases a with
    | nil => simp at hk'
    | cons x a' => simp at hk'; exact ⟨x, a', rfl, hk'⟩
  obtain ⟨m₁, s₁, hp, he, hL₁⟩ := parseEnumMember_reads m s (x :: a') (b ++ c :: rest) hs hl ha' (by simp)
  exact ⟨m₁, s₁, x, a', rfl, by rw [hx]; exact hk1, by rw [hx]; exact hk2, hp, he, hL₁⟩

theorem Laid.length_members : ∀ {members : List EnumMember} {ts : List Token},
    Laid ts (members.map EnumMember.words) → members.length ≤ ts.length
  | [], _, _ => by simp
  | m :: members, ts, h => by
    obtain ⟨a, b, rfl, ha, _, _, hb⟩ := Laid.cons (by simpa using h)
    obtain ⟨k, hk, _, _⟩ := EnumMember.first m
    have : a ≠ [] := by
      intro e; subst e
      have h0 : m.words.flatten = [] := by have := ha.kinds; simpa using this.symm
      rw [h0] at hk; simp at hk
    have := Laid.length_members hb
    cases a with
    | nil => exact absurd rfl ‹_›
    | cons _ _ => simp; omega

/-- `enum`, a name and `{`, the members on their own lines, and `}`. -/
theorem parseEnum_reads (start : Pos) (exported : Bool) (sp : Span) (name : String)
    (members : List EnumMember) (hname : exprName name = true) :
    ∀ (s : ParseState) (ts mts rest : List Token) (rb : Token), s.rest = ts ++ mts ++ rb :: rest →
      s.left = s.rest.length → Touching ts [keywordWord "enum", identWord name, punctWord "{"] →
      Laid mts (members.map EnumMember.words) → rb.kind = .punct "}" → rest ≠ [] →
      ∃ d' s', Parse.parseEnum start exported s = .ok d' s' ∧
        d'.erase = (Decl.enum sp exported name members).erase ∧ Leaves s s' rest := by
  intro s ts mts rest rb hs hl ht hm hrb hr
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  obtain ⟨ek, ts₁, rfl, _, h₁⟩ := Touching.cons_one (by simpa [keywordWord] using ht)
  obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  obtain ⟨lb, ts₃, rfl, hlb, h₃⟩ := Touching.cons_one (by simpa [punctWord] using h₂)
  simp [Touching] at h₃; subst h₃
  have hs' : s.rest = ek :: nm :: lb :: (mts ++ rb :: rest) := by simpa using hs
  let s₁ := past s ek (nm :: (lb :: (mts ++ rb :: rest)))
  let s₂ := past s₁ nm (lb :: (mts ++ rb :: rest))
  let s₃ : ParseState := { s₂ with rest := mts ++ rb :: rest, left := s₂.left - 1, lastStop := lb.span.stop }
  have hl₃ : s₃.left = s₃.rest.length := by simp [s₃, s₂, s₁, hl, hs']
  have hlen := Laid.length_members hm
  obtain ⟨res, s₄, hit, he, hL₄⟩ := enumMember_loop members (10 * (s₃.left + 1)) #[] s₃ mts rest rb
    (by have : s₃.left = mts.length + rest.length + 1 := by simp [s₃, s₂, s₁, hl, hs']; omega
        omega) rfl hrb hl₃ hm
  have hs₄ : s₄.rest = rb :: rest := hL₄.rest_eq
  refine ⟨.enum ⟨start, rb.span.stop⟩ exported name res.toList,
    { s₄ with rest := rest, left := s₄.left - 1, lastStop := rb.span.stop }, ?_, ?_,
    leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])) (leaves_trans hL₄
        (leaves_advance hs₄ (by rw [hL₄.left_eq, hs₄])))))⟩
  · simp only [Parse.parseEnum]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname')]
    rw [Parse.bind_eq (Parse.expectPunct_ok (s := s₂) rfl (by simp) hlb), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_eq hit, Parse.bind_eq (Parse.expectPunct_ok hs₄ hr hrb), Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · simp [Decl.erase] at he ⊢
    exact he


/-! ### Imports -/

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
    let s₁ := past s ty (nm :: (d :: r))
    let s₂ := past s₁ nm (d :: r)
    have hty1 : (ty.kind == .punct "}") = false := by simp [hty]
    rcases hd with hd | hd
    · refine ⟨⟨nm.span, true, n.name⟩, { s₂ with rest := r, left := s₂.left - 1, lastStop := d.span.stop }, ?_,
        by simp [ImportName.erase, hto], ?_⟩
      · simp only [Parse.importStep]
        rw [Parse.bind_eq (Parse.peek_eq hs')]
        rw [if_neg (show ¬ (ty.isPunct "}" = true) by simp [Token.isPunct, hty1]), Parse.pure_bind]
        rw [Parse.bind_eq (Parse.peekAt_rest _ _)]
        simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent,
          Token.isIdent, hty, hnm, beq_self_eq_true, Bool.true_and, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte, Parse.pure_bind, Bool.or_true]
        rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl),
          Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
        rw [if_neg (show ¬ ((d.kind == .ident "as") = true) by simp [hd1]), Parse.pure_bind,
          Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
        rw [if_pos (show d.isPunct "," = true by simp [Token.isPunct, hd]),
          Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₂) rfl (hr hd)))]
        rfl
      · simp only [Token.isPunct, hd, beq_self_eq_true, ↓reduceIte]
        exact leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl
          (by simp [s₁, hl, hs'])) (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs'])))
    · refine ⟨⟨nm.span, true, n.name⟩, s₂, ?_, by simp [ImportName.erase, hto], ?_⟩
      · simp only [Parse.importStep]
        rw [Parse.bind_eq (Parse.peek_eq hs')]
        rw [if_neg (show ¬ (ty.isPunct "}" = true) by simp [Token.isPunct, hty1]), Parse.pure_bind]
        rw [Parse.bind_eq (Parse.peekAt_rest _ _)]
        simp only [hs', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Token.isAnyIdent,
          Token.isIdent, hty, hnm, beq_self_eq_true, Bool.true_and, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte, Parse.pure_bind, Bool.or_true]
        rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (Parse.peek_eq (s := s₁) rfl),
          Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname), Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
        rw [if_neg (show ¬ ((d.kind == .ident "as") = true) by simp [hd1]), Parse.pure_bind,
          Parse.bind_eq (Parse.peek_eq (s := s₂) rfl)]
        rw [if_neg (show ¬ (d.isPunct "," = true) by simp [Token.isPunct, hd]),
          if_neg (show ¬ ((!d.isPunct "}") = true) by simp [Token.isPunct, hd]), Parse.pure_bind]
        rfl
      · have : (d.kind == .punct ",") = false := by simp [hd]
        simp only [Token.isPunct, this, Bool.false_eq_true, ↓reduceIte]
        exact leaves_trans (leaves_advance hs' hl) (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
  · have hs' : s.rest = nm :: d :: r := by simpa using hs
    let s₁ := past s nm (d :: r)
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
        exact leaves_trans (leaves_advance hs' hl) (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
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
        exact leaves_advance hs' hl

/-- The loop of `parseImport` reads the names of an import, with a `,` between two of them, which a `}` follows. -/
theorem import_loop :
    ∀ (names : List ImportName) (fuel : Nat) (acc : Array ImportName) (s : ParseState) (ts rest : List Token)
      (c : Token), (∀ n ∈ names, n.name ∉ Parse.refusedNames) → names.length < fuel →
      s.rest = ts ++ c :: rest → c.kind = .punct "}" → s.left = s.rest.length →
      Touching ts (separated "," (names.map ImportName.words)) →
      ∃ res s', Parse.iterate fuel acc (Parse.importStep false) s = .ok res s' ∧
        res.toList.map ImportName.erase = (acc.toList ++ names).map ImportName.erase ∧ Leaves s s' (c :: rest) := by
  intro names
  induction names with
  | nil =>
    intro fuel acc s ts rest c _ hlen hs hc hl ht
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    have hts : ts = [] := Touching.nil.mp (by simpa [separated] using ht)
    subst hts
    have hs' : s.rest = c :: rest := by simpa using hs
    refine ⟨acc, s, Parse.iterate_false ?_, by simp, Leaves.refl hs' (by simp [hl, hs'])⟩
    simp only [Parse.importStep]
    rw [Parse.bind_eq (Parse.peek_eq hs')]
    simp [Token.isPunct, hc, pure, EStateM.pure]
  | cons n names ih =>
    intro fuel acc s ts rest c hnames hlen hs hc hl ht
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    cases names with
    | nil =>
      have ha : Touching ts n.words := by simpa [separated] using ht
      obtain ⟨n', s₁, hstep, he, hL₁⟩ := importStep_ok (acc := acc) hs hl ha (hnames n (by simp)) (.inr hc)
        (fun h => absurd (hc.symm.trans h) (punct_ne (by decide)))
      have hc' : (c.kind == .punct ",") = false := by simp [hc]
      simp only [Token.isPunct, hc', Bool.false_eq_true, ↓reduceIte] at hL₁
      have hl₁ : s₁.left = s₁.rest.length := by rw [hL₁.left_eq, hL₁.rest_eq]
      obtain ⟨res, s', hit, he', hL'⟩ := ih f' (acc.push n') s₁ [] rest c (by simp) (by simp at hlen ⊢; omega)
        (by simpa using hL₁.rest_eq) hc hl₁ (by simp [separated, Touching])
      refine ⟨res, s', ?_, by rw [he']; simp [he], leaves_trans hL₁ hL'⟩
      rw [Parse.iterate_true hstep]; exact hit
    | cons y ys =>
      obtain ⟨a, more, rfl, ha, hmore⟩ := Touching.append_split (ws₁ := n.words)
        (ws₂ := punctWord "," :: separated "," ((y :: ys).map ImportName.words)) (by simpa [separated] using ht)
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
      (∀ y ∈ ts.tail, NoBreak y) → rest ≠ [] →
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
  let s₁ := past s ik (lb :: (nts ++ rb :: fr :: st :: semi :: rest))
  let s₂ : ParseState := { s₁ with rest := nts ++ rb :: fr :: st :: semi :: rest, left := s₁.left - 1, lastStop := lb.span.stop }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁, hl, hs']
  have hlen := length_items hnts
  obtain ⟨res, s₃, hit, he, hL₃⟩ := import_loop names (10 * (s₂.left + 1)) #[] s₂ nts (fr :: st :: semi :: rest) rb
    hnames (by have h4 : s₂.left = nts.length + rest.length + 4 := (by simp [s₂, s₁, hl, hs']; omega); omega)
    rfl hrb hl₂ hnts
  have hs₃ : s₃.rest = rb :: fr :: st :: semi :: rest := hL₃.rest_eq
  let s₄ : ParseState := { s₃ with rest := fr :: st :: semi :: rest, left := s₃.left - 1, lastStop := rb.span.stop }
  let s₅ := past s₄ fr (st :: (semi :: rest))
  let s₆ := past s₅ st (semi :: rest)
  have hres : res.isEmpty = false := by
    cases hres : res.toList with
    | nil => rw [hres] at he; cases names with
      | nil => exact absurd rfl hne
      | cons _ _ => simp at he
    | cons _ _ => simp [← Array.toList_eq_nil_iff, hres]
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
  · simp [Decl.erase] at he ⊢
    exact he
  · exact leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans hL₃ (leaves_trans (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃]))
        (leaves_trans (leaves_advance (s := s₄) rfl (by simp [s₄, hL₃.left_eq]))
          (leaves_trans (leaves_advance (s := s₅) rfl (by simp [s₅, s₄, hL₃.left_eq]))
            (leaves_advance (s := s₆) rfl (by simp [s₆, s₅, s₄, hL₃.left_eq])))))))

/-! ### Declarations -/

/-- A statement at the top of a module starts with no `import`, `export` or
`function`, and a name after `interface` or `type` at its start is not on the
same line, so `parseDecl` hands it to `parseStatement`. -/
theorem Stmt.declStart {T : Edition} (st : Stmt) (hw : st.wf T false false = true) {ts : List Token}
    (ht : Laid ts st.wordLines) :
    ∃ x ts', ts = x :: ts' ∧ x.kind ≠ .keyword "import" ∧ x.kind ≠ .keyword "export" ∧
      x.kind ≠ .keyword "function" ∧ x.kind ≠ .keyword "enum" ∧ x.kind ≠ .keyword "class" ∧
      ((x.kind = .ident "interface" ∨ x.kind = .ident "type") → ∃ y ts'', ts' = y :: ts'' ∧ y.isAnyIdent = false) := by
  cases st with
  | exprStmt sp e =>
    simp only [Stmt.wf, Bool.and_eq_true] at hw
    obtain ⟨⟨hwe, _⟩, hk⟩ := hw
    have hsp := Expr.spineOK_wf e .assign hwe
    simp only [Stmt.wordLines, Stmt.lines, List.map_cons, List.map_nil] at ht
    obtain ⟨h1, _⟩ := Laid.one ht
    obtain ⟨ets, ts₁, rfl, het, h'⟩ := Touching.append_split h1
    obtain ⟨semi, ts₂, rfl, hsemi, h''⟩ := Touching.cons_one (by simpa [punctWord] using h')
    simp [Touching] at h''; subst h''
    obtain ⟨x, ets', rfl, hx⟩ := Touching.head het
    have hke := het.kinds
    have hxk : startsExprStmt (some x.kind) = true := by
      have : e.tokens.head? = some x.kind := by simp only [Expr.tokens, ← hke]; simp
      rw [← this]; exact hk
    refine ⟨x, ets' ++ [semi], by simp, ?_, ?_, ?_, ?_, ?_, fun h => ?_⟩
    · intro h; rw [h] at hxk; simp [startsExprStmt] at hxk
    · intro h; rw [h] at hxk; simp [startsExprStmt] at hxk
    · intro h; rw [h] at hxk; simp [startsExprStmt] at hxk
    · intro h; rw [h] at hxk; simp [startsExprStmt] at hxk
    · intro h; rw [h] at hxk; simp [startsExprStmt] at hxk
    · cases ets' with
      | nil => exact ⟨semi, [], by simp, by simp [Token.isAnyIdent, hsemi]⟩
      | cons y ets'' =>
        refine ⟨y, ets'' ++ [semi], by simp, ?_⟩
        have hn : NotIdent y.kind := by
          rcases h with h | h
          · exact Expr.second e (n := "interface") (k := y.kind) (r := ets''.map (·.kind)) hsp (by decide)
              (by simp only [Expr.tokens, ← hke, List.map_cons, h])
          · exact Expr.second e (n := "type") (k := y.kind) (r := ets''.map (·.kind)) hsp (by decide)
              (by simp only [Expr.tokens, ← hke, List.map_cons, h])
        cases hy : y.kind <;> simp [Token.isAnyIdent, hy, NotIdent] at hn ⊢
  | varDecl sp d =>
    simp only [Stmt.wordLines, Stmt.lines, List.map_cons, List.map_nil] at ht
    obtain ⟨h1, _⟩ := Laid.one ht
    simp only [VarDecl.words, VarKind.word_eq] at h1
    obtain ⟨x, ts', rfl, hx, _⟩ := Touching.cons_one (by simpa using h1)
    refine ⟨x, ts', rfl, ?_, ?_, ?_, ?_, ?_, fun h => ?_⟩
    · rw [hx]; cases d.kind <;> simp [VarKind.token]
    · rw [hx]; cases d.kind <;> simp [VarKind.token]
    · rw [hx]; cases d.kind <;> simp [VarKind.token]
    · rw [hx]; cases d.kind <;> simp [VarKind.token]
    · rw [hx]; cases d.kind <;> simp [VarKind.token]
    · exfalso; rw [hx] at h; revert h; cases d.kind <;> simp [VarKind.token]
  | destructure sp kind p type init =>
    simp only [Stmt.wordLines, Stmt.lines, List.map_cons, List.map_nil] at ht
    obtain ⟨h1, _⟩ := Laid.one ht
    simp only [destructureWords, VarKind.word_eq] at h1
    obtain ⟨x, ts', rfl, hx, _⟩ := Touching.cons_one (by simpa using h1)
    refine ⟨x, ts', rfl, ?_, ?_, ?_, ?_, ?_, fun h => ?_⟩
    · rw [hx]; cases kind <;> simp [VarKind.token]
    · rw [hx]; cases kind <;> simp [VarKind.token]
    · rw [hx]; cases kind <;> simp [VarKind.token]
    · rw [hx]; cases kind <;> simp [VarKind.token]
    · rw [hx]; cases kind <;> simp [VarKind.token]
    · exfalso; rw [hx] at h; revert h; cases kind <;> simp [VarKind.token]
  | funDecl _ _ _ _ _ _ => simp [Stmt.wf] at hw
  | _ =>
    obtain ⟨x, ts', rfl, hfirst⟩ := Laid.first hw ht
    have hk := ht.kinds
    refine ⟨x, ts', rfl, ?_⟩
    first
    | (simp [Stmt.wordLines, Stmt.lines, keywordWord, punctWord] at hk; rw [hk.1]; simp)
    | (rename_i e; cases e <;> simp [Stmt.wordLines, Stmt.lines, keywordWord, punctWord] at hk <;> rw [hk.1] <;> simp)



/-- The constructor of an error class that `parseClass` reads: parameters
that `parseParam` reads, with `?` allowed as in a function, and a message
that ends at `)`. -/
def ctorWF (T : Edition) : Option (List CtorParam × Expr) → Bool
  | none => true
  | some (ps, m) => ps.all (fun p => p.param.wf) && m.wfParen T

/-- `d` is a declaration that `parseDecl` reads when the target edition is `T`. -/
def Decl.wf (T : Edition) : Decl → Bool
  | .«import» _ names _ => !names.isEmpty && names.all (fun n => exprName n.name)
  | .exports _ names _ => !names.isEmpty && names.all (fun n => exprName n.name)
  | .function _ _ name tps params rt body => exprName name && tps.all typeName && params.all Param.wf &&
      (match rt with | some t => t.wf | none => true) && body.isBlock && body.wf T true false
  | .interface _ _ name tps fields => exprName name && tps.all typeName && fields.all (fun f => f.type.wf)
  | .typeAlias _ _ name tps ty => exprName name && tps.all typeName && ty.wf
  | .enum _ _ name _ => exprName name
  | .errorClass _ _ name ctor => exprName name && ctorWF T ctor
  | .exportedVar _ d => d.wf T
  | .stmt s => s.wf T false false

/-- A declaration that ends with an `if` without `else`. -/
def Decl.openIf : Decl → Bool
  | .stmt s => s.openIf
  | _ => false

def Decl.wordLines (d : Decl) : List (List Word) := d.lines.map Prod.snd

/-- `p` reads the tokens of the lines of `d` at the top of a module, followed by
any rest, as `d` apart from spans, and leaves the rest. -/
def ReadsD (T : Edition) (p : ParseM Decl) (d : Decl) : Prop :=
  ∀ (s : ParseState) (ts rest : List Token), s.target = T → s.inFunction = false →
    s.rest = ts ++ rest → s.left = s.rest.length → Laid ts d.wordLines → rest ≠ [] →
    (d.openIf = true → ∀ u ∈ rest.head?, u.kind ≠ .keyword "else") →
    ∃ d' s', p s = .ok d' s' ∧ d'.erase = d.erase ∧ Leaves s s' rest

/-- `startsExportList` only looks at the next two tokens. -/
theorem startsExportList_eq (s : ParseState) :
    Parse.startsExportList s = .ok ((s.rest[0]?.getD s.eof).isPunct "{" ||
      ((s.rest[0]?.getD s.eof).isIdent "type" && (s.rest[1]?.getD s.eof).isPunct "{")) s := by
  simp [Parse.startsExportList, Parse.peek, Parse.peekAt, get, getThe, MonadStateOf.get, EStateM.get, bind,
    EStateM.bind, pure, EStateM.pure]

/-- No export list starts at a token that is not `{`, unless it is `type` and
a `{` follows it. -/
theorem startsExportList_no {s : ParseState} {y z : Token} {r : List Token} (hs : s.rest = y :: z :: r)
    (hy : y.kind ≠ .punct "{") (hz : y.kind = .ident "type" → z.kind ≠ .punct "{") :
    Parse.startsExportList s = .ok false s := by
  rw [startsExportList_eq, hs]
  by_cases ht : y.kind = .ident "type"
  · simp [Token.isPunct, Token.isIdent, hy, hz ht]
  · simp [Token.isPunct, Token.isIdent, hy, ht]

/-- No export list starts at a token that is neither `{` nor `type`. -/
theorem startsExportList_head {s : ParseState} {y : Token} {r : List Token} (hs : s.rest = y :: r)
    (hy : y.kind ≠ .punct "{") (ht : y.kind ≠ .ident "type") : Parse.startsExportList s = .ok false s := by
  rw [startsExportList_eq, hs]; simp [Token.isPunct, Token.isIdent, hy, ht]

/-- `parseDecl` reads `export`, when it comes, and goes on with
`parseDeclBody` when no export list follows. -/
theorem parseDecl_body {s : ParseState} {x : Token} {r : List Token} (hs : s.rest = x :: r) (hr : r ≠ [])
    (hx : x.kind ≠ .keyword "import")
    (hb : x.isKeyword "export" = true → Parse.startsExportList (past s x r) = .ok false (past s x r)) :
    Parse.parseDecl s = Parse.parseDeclBody x.span.start (x.isKeyword "export")
      (if x.isKeyword "export" then past s x r else s) := by
  simp only [Parse.parseDecl]
  rw [Parse.bind_eq (Parse.peek_eq hs)]
  rw [if_neg (show ¬ (x.isKeyword "import" = true) by simp [Token.isKeyword, hx]), Parse.pure_bind]
  by_cases he : x.isKeyword "export" = true
  · rw [if_pos he, Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs hr)), Parse.bind_eq (hb he)]
    simp only [he, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind]
  · rw [if_neg he, Parse.pure_bind, Parse.bind_eq (startsExportList_eq s)]
    simp only [he, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind]

theorem parseDeclBody_function {s : ParseState} {t : Token} {r : List Token} (start : Pos) (e : Bool)
    (hs : s.rest = t :: r) (ht : t.kind = .keyword "function") :
    Parse.parseDeclBody start e s = Parse.parseFunction start e s := by
  simp only [Parse.parseDeclBody]
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.peekAt_rest _ _)]
  rw [if_pos (show t.isKeyword "function" = true by simp [Token.isKeyword, ht])]

theorem parseDeclBody_interface {s : ParseState} {t nm : Token} {r : List Token} {n : String} (start : Pos)
    (e : Bool) (hs : s.rest = t :: nm :: r) (ht : t.kind = .ident "interface") (hnm : nm.kind = .ident n)
    (hnl : nm.newlineBefore = false) :
    Parse.parseDeclBody start e s = Parse.parseInterface start e s := by
  simp only [Parse.parseDeclBody]
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.peekAt_rest _ _)]
  simp only [hs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  rw [if_neg (show ¬ (t.isKeyword "function" = true) by simp [Token.isKeyword, ht])]
  rw [if_pos (show (t.isIdent "interface" && (nm.isAnyIdent && !nm.newlineBefore)) = true by
    simp [Token.isIdent, Token.isAnyIdent, ht, hnm, hnl])]

theorem parseDeclBody_typeAlias {s : ParseState} {t nm : Token} {r : List Token} {n : String} (start : Pos)
    (e : Bool) (hs : s.rest = t :: nm :: r) (ht : t.kind = .ident "type") (hnm : nm.kind = .ident n)
    (hnl : nm.newlineBefore = false) :
    Parse.parseDeclBody start e s = Parse.parseTypeAlias start e s := by
  simp only [Parse.parseDeclBody]
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.peekAt_rest _ _)]
  simp only [hs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  rw [if_neg (show ¬ (t.isKeyword "function" = true) by simp [Token.isKeyword, ht])]
  rw [if_neg (show ¬ ((t.isIdent "interface" && (nm.isAnyIdent && !nm.newlineBefore)) = true) by
    simp [Token.isIdent, ht])]
  rw [if_pos (show (t.isIdent "type" && (nm.isAnyIdent && !nm.newlineBefore)) = true by
    simp [Token.isIdent, Token.isAnyIdent, ht, hnm, hnl])]

/-- A statement at the top of a module. -/
theorem parseDecl_stmt {T : Edition} (st : Stmt) (hw : st.wf T false false = true) :
    ReadsD T Parse.parseDecl (.stmt st) := by
  intro s ts rest hT hF hs hl ht hr hopen
  have ht' : Laid ts st.wordLines := by simpa [Decl.wordLines, Decl.lines, Stmt.wordLines] using ht
  obtain ⟨x, ts', rfl, h1, h2, h3, h5, h6, h4⟩ := Stmt.declStart st hw ht'
  obtain ⟨st', s', hp, he, hL⟩ := parseStatement_budget (loop := false) st hw s _ rest hT hF (fun h => by cases h)
    hs hl ht' hr hopen
  refine ⟨.stmt st', s', ?_, by simp [Decl.erase, he], hL⟩
  have hs' : s.rest = x :: (ts' ++ rest) := by simpa using hs
  have hc : ∀ n, (n = "interface" ∨ n = "type") →
      (x.isIdent n && ((s.rest[1]?.getD s.eof).isAnyIdent && !(s.rest[1]?.getD s.eof).newlineBefore)) = false := by
    intro n hn
    rcases Classical.em (x.kind = .ident n) with hx | hx
    · obtain ⟨y, ts'', rfl, hy⟩ := h4 (by rcases hn with rfl | rfl <;> simp [hx])
      simp [hs', hy]
    · simp [Token.isIdent, hx]
  have hne : ¬ (x.isKeyword "export" = true) := by simp [Token.isKeyword, h2]
  rw [parseDecl_body hs' (by simp [hr]) h1 (fun h => absurd h hne), if_neg hne]
  simp only [Parse.parseDeclBody]
  rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.peekAt_rest _ _)]
  rw [if_neg (show ¬ (x.isKeyword "function" = true) by simp [Token.isKeyword, h3])]
  rw [if_neg (show ¬ ((x.isIdent "interface" && ((s.rest[1]?.getD s.eof).isAnyIdent &&
      !(s.rest[1]?.getD s.eof).newlineBefore)) = true) by simp [hc "interface" (.inl rfl)])]
  rw [if_neg (show ¬ ((x.isIdent "type" && ((s.rest[1]?.getD s.eof).isAnyIdent &&
      !(s.rest[1]?.getD s.eof).newlineBefore)) = true) by simp [hc "type" (.inr rfl)])]
  rw [if_neg (show ¬ (x.isKeyword "enum" = true) by simp [Token.isKeyword, h5])]
  rw [if_neg (show ¬ (x.isKeyword "class" = true) by simp [Token.isKeyword, h6])]
  rw [if_neg hne]
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hp]
  rfl


/-- `{ names } from "source";` or `{ names };`, after `export`. -/
theorem parseExportList_reads (start : Pos) (sp : Span) (names : List ImportName) (source : Option String)
    (hne : names ≠ []) (hnames : ∀ n ∈ names, n.name ∉ Parse.refusedNames) :
    ∀ (s : ParseState) (ts rest : List Token), s.rest = ts ++ rest → s.left = s.rest.length →
      Touching ts (enclose "{" "}" (names.map ImportName.words) ++ fromWords source ++ [punctWord ";"]) →
      (∀ y ∈ ts.tail, NoBreak y) → rest ≠ [] →
      ∃ d' s', Parse.parseExportList start s = .ok d' s' ∧ d'.erase = (Decl.exports sp names source).erase ∧
        Leaves s s' rest := by
  intro s ts rest hs hl ht hn hr
  obtain ⟨its, ts₂, rfl, hits, h₂⟩ := Touching.append_split (by simpa [List.append_assoc] using ht)
  obtain ⟨lb, nts, rb, rfl, hlb, hnts, hrb⟩ := Touching.enclosed (by simpa [enclose] using hits)
  have hs' : s.rest = lb :: (nts ++ rb :: (ts₂ ++ rest)) := by simpa using hs
  let s₂ : ParseState := { s with rest := nts ++ rb :: (ts₂ ++ rest), left := s.left - 1, lastStop := lb.span.stop }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, hl, hs']
  have hlen := length_items hnts
  obtain ⟨res, s₃, hit, he, hL₃⟩ := import_loop names (10 * (s₂.left + 1)) #[] s₂ nts (ts₂ ++ rest) rb
    hnames (by have h4 : s₂.left = nts.length + ts₂.length + rest.length + 1 := (by simp [s₂, hl, hs']; omega); omega)
    rfl hrb hl₂ hnts
  have hs₃ : s₃.rest = rb :: (ts₂ ++ rest) := hL₃.rest_eq
  let s₄ : ParseState := { s₃ with rest := ts₂ ++ rest, left := s₃.left - 1, lastStop := rb.span.stop }
  have hl₄ : s₄.left = s₄.rest.length := by simp [s₄, hL₃.left_eq]
  have hres : res.isEmpty = false := by
    cases hres : res.toList with
    | nil => rw [hres] at he; cases names with
      | nil => exact absurd rfl hne
      | cons _ _ => simp at he
    | cons _ _ => simp [← Array.toList_eq_nil_iff, hres]
  have hdone : Leaves s s₄ (ts₂ ++ rest) :=
    leaves_trans (leaves_advance hs' hl) (leaves_trans hL₃ (leaves_advance hs₃ (by rw [hL₃.left_eq, hs₃])))
  cases source with
  | none =>
    obtain ⟨semi, ts₅, rfl, hsemi, h₅⟩ := Touching.cons_one (by simpa [fromWords, punctWord] using h₂)
    simp [Touching] at h₅; subst h₅
    refine ⟨.exports ⟨start, semi.span.stop⟩ res.toList none,
      { s₄ with rest := rest, left := s₄.left - 1, lastStop := semi.span.stop }, ?_, ?_, ?_⟩
    · simp only [Parse.parseExportList]
      rw [Parse.bind_eq (Parse.peek_eq hs')]
      rw [if_neg (show ¬ (lb.isIdent "type" = true) by simp [Token.isIdent, hlb]), Parse.pure_bind]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs' (by simp))), Parse.bind_eq (Parse.budget_eq _),
        Parse.bind_eq hit, Parse.bind_eq (Parse.expectPunct_ok hs₃ (by simp) hrb)]
      rw [if_neg (show ¬ (res.isEmpty = true) by simp [hres]), Parse.pure_bind]
      rw [Parse.bind_eq (Parse.peek_eq (s := s₄) rfl)]
      rw [if_pos (show (!semi.isIdent "from") = true by simp [Token.isIdent, hsemi])]
      rw [Parse.bind_eq (endStatement_semi (s := s₄) rfl hr hsemi), Parse.bind_eq (Parse.spanFrom_eq _ _)]
      rfl
    · simp [Decl.erase] at he ⊢
      exact he
    · exact leaves_trans hdone (leaves_advance (s := s₄) rfl hl₄)
  | some src =>
    obtain ⟨fr, ts₃, rfl, hfr, h₃⟩ := Touching.cons_one (by simpa [fromWords, identWord] using h₂)
    obtain ⟨st, ts₄, rfl, hst, h₄⟩ := Touching.cons_one h₃
    obtain ⟨semi, ts₅, rfl, hsemi, h₅⟩ := Touching.cons_one (by simpa [punctWord] using h₄)
    simp [Touching] at h₅; subst h₅
    let s₅ := past s₄ fr (st :: (semi :: rest))
    let s₆ := past s₅ st (semi :: rest)
    refine ⟨.exports ⟨start, semi.span.stop⟩ res.toList (some src),
      { s₆ with rest := rest, left := s₆.left - 1, lastStop := semi.span.stop }, ?_, ?_, ?_⟩
    · simp only [Parse.parseExportList]
      rw [Parse.bind_eq (Parse.peek_eq hs')]
      rw [if_neg (show ¬ (lb.isIdent "type" = true) by simp [Token.isIdent, hlb]), Parse.pure_bind]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs' (by simp))), Parse.bind_eq (Parse.budget_eq _),
        Parse.bind_eq hit, Parse.bind_eq (Parse.expectPunct_ok hs₃ (by simp) hrb)]
      rw [if_neg (show ¬ (res.isEmpty = true) by simp [hres]), Parse.pure_bind]
      rw [Parse.bind_eq (Parse.peek_eq (s := s₄) rfl)]
      rw [if_neg (show ¬ ((!fr.isIdent "from") = true) by simp [Token.isIdent, hfr]), Parse.pure_bind,
        Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₄) (t := fr) (u := st) (r := semi :: rest) rfl)),
        Parse.bind_eq (Parse.advance_eq (s := s₅) (t := st) (u := semi) (r := rest) rfl)]
      simp only [hst]
      rw [Parse.bind_eq (endStatement_semi (s := s₆) rfl hr hsemi), Parse.bind_eq (Parse.spanFrom_eq _ _)]
      rfl
    · simp [Decl.erase] at he ⊢
      exact he
    · exact leaves_trans hdone (leaves_trans (leaves_advance (s := s₄) rfl hl₄)
        (leaves_trans (leaves_advance (s := s₅) rfl (by simp [s₅, s₄, hL₃.left_eq]))
          (leaves_advance (s := s₆) rfl (by simp [s₆, s₅, s₄, hL₃.left_eq]))))

theorem parseDecl_exports {T : Edition} (sp : Span) (names : List ImportName) (source : Option String)
    (hw : (Decl.exports sp names source).wf T = true) :
    ReadsD T Parse.parseDecl (.exports sp names source) := by
  intro s ts rest _ _ hs hl ht hr _
  simp only [Decl.wf, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hw
  obtain ⟨hne, hn⟩ := hw
  simp only [Decl.wordLines, Decl.lines, List.map_cons, List.map_nil] at ht
  obtain ⟨h1, hnl⟩ := Laid.one ht
  obtain ⟨ek, ts', rfl, hek, h₁⟩ := Touching.cons_one (by simpa [keywordWord] using h1)
  have hs' : s.rest = ek :: (ts' ++ rest) := by simpa using hs
  obtain ⟨d', s', hp, he, hL⟩ := parseExportList_reads ek.span.start sp names source
    (by simpa using hne) (fun n hn' => by simpa [exprName] using hn n hn') (past s ek (ts' ++ rest)) ts' rest rfl
    (by simp [hl, hs']) (by simpa [List.append_assoc] using h₁) (fun y hy => hnl y (by simp [List.mem_of_mem_tail hy]))
    hr
  refine ⟨d', s', ?_, he, leaves_trans (leaves_advance hs' hl) hL⟩
  obtain ⟨lb, ts'', hts, hlb⟩ : ∃ lb ts'', ts' = lb :: ts'' ∧ lb.kind = .punct "{" := by
    obtain ⟨its, _, rfl, hits, _⟩ := Touching.append_split (by simpa [List.append_assoc] using h₁)
    obtain ⟨lb, nts, rb, rfl, hlb, _, _⟩ := Touching.enclosed (by simpa [enclose] using hits)
    exact ⟨lb, _, rfl, hlb⟩
  subst hts
  simp only [Parse.parseDecl]
  rw [Parse.bind_eq (Parse.peek_eq hs')]
  rw [if_neg (show ¬ (ek.isKeyword "import" = true) by simp [Token.isKeyword, hek]), Parse.pure_bind]
  rw [if_pos (show ek.isKeyword "export" = true by simp [Token.isKeyword, hek]),
    Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs' (by simp))), Parse.bind_eq (startsExportList_eq _)]
  simp only [List.cons_append, List.getElem?_cons_zero, Option.getD_some, Token.isPunct, hlb, beq_self_eq_true,
    Bool.true_or, Token.isKeyword, hek, Bool.and_self, ↓reduceIte]
  exact (Parse.bind_eq hp).trans rfl

theorem parseDecl_import {T : Edition} (sp : Span) (names : List ImportName) (source : String)
    (hw : (Decl.«import» sp names source).wf T = true) :
    ReadsD T Parse.parseDecl (.«import» sp names source) := by
  intro s ts rest _ _ hs hl ht hr _
  simp only [Decl.wf, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hw
  obtain ⟨hne, hn⟩ := hw
  simp only [Decl.wordLines, Decl.lines, List.map_cons, List.map_nil] at ht
  obtain ⟨h1, hnl⟩ := Laid.one ht
  obtain ⟨ik, ts', rfl, hik, _⟩ := Touching.cons_one (by simpa [keywordWord] using h1)
  obtain ⟨d', s', hp, he, hL⟩ := parseImport_reads ik.span.start sp names source
    (by simpa using hne) (fun n hn' => by simpa [exprName] using hn n hn') s _ rest hs hl h1 hnl hr
  refine ⟨d', s', ?_, he, hL⟩
  simp only [Parse.parseDecl]
  rw [Parse.bind_eq (Parse.peek_eq (by simpa using hs))]
  rw [if_pos (show ik.isKeyword "import" = true by simp [Token.isKeyword, hik])]
  rw [Parse.bind_eq hp]
  rfl


theorem parseDecl_typeAlias {T : Edition} (sp : Span) (exported : Bool) (name : String) (tps : List String)
    (ty : TypeExpr) (hw : (Decl.typeAlias sp exported name tps ty).wf T = true) :
    ReadsD T Parse.parseDecl (.typeAlias sp exported name tps ty) := by
  intro s ts rest _ _ hs hl ht hr _
  simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true] at hw
  obtain ⟨⟨hname, htps⟩, hty⟩ := hw
  simp only [Decl.wordLines, Decl.lines, List.map_cons, List.map_nil] at ht
  obtain ⟨h1, hnl⟩ := Laid.one ht
  cases exported with
  | false =>
    simp only [exportWords, Bool.false_eq_true, ↓reduceIte, List.nil_append] at h1
    obtain ⟨tk, ts₁, rfl, htk, h₁⟩ := Touching.cons_one (by simpa [identWord] using h1)
    obtain ⟨nm, ts₂, rfl, hnm, _⟩ := Touching.cons_one (by simpa [identWord] using h₁)
    have hs' : s.rest = tk :: nm :: (ts₂ ++ rest) := by simpa using hs
    obtain ⟨d', s', hp, he, hL⟩ := parseTypeAlias_reads tk.span.start (tk.isKeyword "export") sp name tps ty hname htps hty
      s _ rest hs hl (by simpa using h1) hnl hr
    have hnmn : nm.newlineBefore = false := hnl nm (by simp) (by rw [hnm]; simp)
    refine ⟨d', s', ?_, by rw [he]; simp [Decl.erase, Token.isKeyword, htk], hL⟩
    rw [parseDecl_body hs' (by simp) (by rw [htk]; simp) (fun h => by simp [Token.isKeyword, htk] at h),
      if_neg (show ¬ (tk.isKeyword "export" = true) by simp [Token.isKeyword, htk]),
      parseDeclBody_typeAlias _ _ hs' htk hnm hnmn]
    exact hp
  | true =>
    simp only [exportWords, ↓reduceIte, List.singleton_append] at h1
    obtain ⟨ex, ts₀, rfl, hex, h₀⟩ := Touching.cons_one (by simpa [keywordWord] using h1)
    obtain ⟨tk, ts₁, rfl, htk, h₁⟩ := Touching.cons_one (by simpa [identWord] using h₀)
    obtain ⟨nm, ts₂, rfl, hnm, _⟩ := Touching.cons_one (by simpa [identWord] using h₁)
    have hs' : s.rest = ex :: tk :: nm :: (ts₂ ++ rest) := by simpa using hs
    let s₁ := past s ex (tk :: (nm :: (ts₂ ++ rest)))
    obtain ⟨d', s', hp, he, hL⟩ := parseTypeAlias_reads ex.span.start (ex.isKeyword "export") sp name tps ty
      hname htps hty s₁ (tk :: nm :: ts₂) rest rfl (by simp [s₁, hl, hs']) (by simpa using h₀) (fun y hy => hnl y (by simp at hy ⊢; simp [hy])) hr
    have hnmn : nm.newlineBefore = false := hnl nm (by simp) (by rw [hnm]; simp)
    refine ⟨d', s', ?_, by rw [he]; simp [Decl.erase, Token.isKeyword, hex], leaves_trans (leaves_advance hs' hl) hL⟩
    rw [parseDecl_body hs' (by simp) (by rw [hex]; simp) (fun _ => startsExportList_no rfl (by rw [htk]; simp) (fun _ => by rw [hnm]; simp)),
      if_pos (show ex.isKeyword "export" = true by simp [Token.isKeyword, hex]),
      parseDeclBody_typeAlias (s := s₁) _ _ rfl htk hnm hnmn]
    exact hp


theorem parseDecl_interface {T : Edition} (sp : Span) (exported : Bool) (name : String) (tps : List String)
    (fields : List Field) (hw : (Decl.interface sp exported name tps fields).wf T = true) :
    ReadsD T Parse.parseDecl (.interface sp exported name tps fields) := by
  intro s ts rest _ _ hs hl ht hr _
  simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true] at hw
  obtain ⟨⟨hname, htps⟩, hfs⟩ := hw
  simp only [Decl.wordLines, Decl.lines, List.map_cons, List.map_append, List.map_map, List.map_nil] at ht
  obtain ⟨a, b, rfl, ha, hna, _, hb⟩ := Laid.cons ht
  obtain ⟨fts, b₂, rfl, hfts, hb₂, _⟩ := Laid.append (l₁ := fields.map Field.words) (by simpa [Function.comp_def] using hb)
  obtain ⟨hrb, _⟩ := Laid.one hb₂
  obtain ⟨rb, b₂', rfl, hrbk, h'⟩ := Touching.cons_one (by simpa [punctWord] using hrb)
  simp [Touching] at h'; subst h'
  cases exported with
  | false =>
    simp only [exportWords, Bool.false_eq_true, ↓reduceIte, List.nil_append] at ha
    obtain ⟨it, a₁, rfl, hit, h₁⟩ := Touching.cons_one (by simpa [identWord] using ha)
    obtain ⟨nm, a₂, rfl, hnm, _⟩ := Touching.cons_one (by simpa [identWord] using h₁)
    have hs' : s.rest = it :: nm :: (a₂ ++ (fts ++ rb :: rest)) := by simpa using hs
    obtain ⟨d', s', hp, he, hL⟩ := parseInterface_reads it.span.start (it.isKeyword "export") sp name tps fields hname
      htps hfs s (it :: nm :: a₂) fts rest rb (by simpa using hs) hl (by simpa using ha) hfts hrbk hr
    have hnmn : nm.newlineBefore = false := hna nm (by simp) (by rw [hnm]; simp)
    refine ⟨d', s', ?_, by rw [he]; simp [Decl.erase, Token.isKeyword, hit], hL⟩
    rw [parseDecl_body hs' (by simp) (by rw [hit]; simp) (fun h => by simp [Token.isKeyword, hit] at h),
      if_neg (show ¬ (it.isKeyword "export" = true) by simp [Token.isKeyword, hit]),
      parseDeclBody_interface _ _ hs' hit hnm hnmn]
    exact hp
  | true =>
    simp only [exportWords, ↓reduceIte, List.singleton_append] at ha
    obtain ⟨ex, a₀, rfl, hex, h₀⟩ := Touching.cons_one (by simpa [keywordWord] using ha)
    obtain ⟨it, a₁, rfl, hit, h₁⟩ := Touching.cons_one (by simpa [identWord] using h₀)
    obtain ⟨nm, a₂, rfl, hnm, _⟩ := Touching.cons_one (by simpa [identWord] using h₁)
    have hs' : s.rest = ex :: it :: nm :: (a₂ ++ (fts ++ rb :: rest)) := by simpa using hs
    let s₁ := past s ex (it :: (nm :: (a₂ ++ (fts ++ rb :: rest))))
    obtain ⟨d', s', hp, he, hL⟩ := parseInterface_reads ex.span.start (ex.isKeyword "export") sp name tps fields hname
      htps hfs s₁ (it :: nm :: a₂) fts rest rb (by simp [s₁]) (by simp [s₁, hl, hs']) (by simpa using h₀) hfts
      hrbk hr
    have hnmn : nm.newlineBefore = false := hna nm (by simp) (by rw [hnm]; simp)
    refine ⟨d', s', ?_, by rw [he]; simp [Decl.erase, Token.isKeyword, hex], leaves_trans (leaves_advance hs' hl) hL⟩
    rw [parseDecl_body hs' (by simp) (by rw [hex]; simp) (fun _ => startsExportList_head rfl (by rw [hit]; simp) (by rw [hit]; simp)),
      if_pos (show ex.isKeyword "export" = true by simp [Token.isKeyword, hex]),
      parseDeclBody_interface (s := s₁) _ _ rfl hit hnm hnmn]
    exact hp


theorem parseDeclBody_enum {s : ParseState} {t nm : Token} {r : List Token} (start : Pos)
    (e : Bool) (hs : s.rest = t :: nm :: r) (ht : t.kind = .keyword "enum") :
    Parse.parseDeclBody start e s = Parse.parseEnum start e s := by
  simp only [Parse.parseDeclBody]
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.peekAt_rest _ _)]
  rw [if_neg (show ¬ (t.isKeyword "function" = true) by simp [Token.isKeyword, ht])]
  rw [if_neg (show ¬ ((t.isIdent "interface" && _) = true) by simp [Token.isIdent, ht])]
  rw [if_neg (show ¬ ((t.isIdent "type" && _) = true) by simp [Token.isIdent, ht])]
  rw [if_pos (show t.isKeyword "enum" = true by simp [Token.isKeyword, ht])]

theorem parseDeclBody_class {s : ParseState} {t nm : Token} {r : List Token} (start : Pos)
    (e : Bool) (hs : s.rest = t :: nm :: r) (ht : t.kind = .keyword "class") :
    Parse.parseDeclBody start e s = Parse.parseClass start e s := by
  simp only [Parse.parseDeclBody]
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.peekAt_rest _ _)]
  rw [if_neg (show ¬ (t.isKeyword "function" = true) by simp [Token.isKeyword, ht])]
  rw [if_neg (show ¬ ((t.isIdent "interface" && _) = true) by simp [Token.isIdent, ht])]
  rw [if_neg (show ¬ ((t.isIdent "type" && _) = true) by simp [Token.isIdent, ht])]
  rw [if_neg (show ¬ (t.isKeyword "enum" = true) by simp [Token.isKeyword, ht])]
  rw [if_pos (show t.isKeyword "class" = true by simp [Token.isKeyword, ht])]

/-- A parameter of a constructor, with `readonly` before it or not. The name
is not followed by a name, so `readonly` before a name is the modifier, and a
parameter named `readonly` is a name. -/
theorem parseCtorParam_reads {T : Edition} (p : CtorParam) (hp : p.param.wf = true) :
    ReadsW T CtorParam.erase CtorParam.words (fun _ _ => true) Parse.parseCtorParam p (EndsItem ")") := by
  intro s ts rest hT hs hl ht hn hr hE _
  obtain ⟨ro, q⟩ := p
  have hread := parseParam_reads (T := T) (ok := true) q hp (fun _ => rfl)
  -- The token after the name is a punctuator: `?`, `:`, `,` or `)`.
  have hafter : ∀ (ts' : List Token), Touching ts' (optionalMark q.optional ++ typeAnnotation q.type) →
      ∀ y, (ts' ++ rest).head? = some y → y.isAnyIdent = false := by
    intro ts' h' y hy
    obtain ⟨u, r, rfl, hu⟩ := hE
    cases ho : q.optional with
    | true =>
      rw [ho] at h'
      obtain ⟨qm, _, rfl, hqm, _⟩ := Touching.cons_one (by simpa [optionalMark, punctWord] using h')
      simp at hy; subst hy; simp [Token.isAnyIdent, hqm]
    | false =>
      rw [ho] at h'
      cases hty : q.type with
      | none =>
        rw [hty] at h'
        simp [Touching, optionalMark, typeAnnotation] at h'; subst h'
        simp at hy; subst hy
        rcases hu with h | h <;> simp [Token.isAnyIdent, h]
      | some t =>
        rw [hty] at h'
        obtain ⟨colon, _, rfl, hcolon, _⟩ :=
          Touching.cons_one (by simpa [punctWord, typeAnnotation, optionalMark] using h')
        simp at hy; subst hy; simp [Token.isAnyIdent, hcolon]
  cases ro with
  | false =>
    simp only [CtorParam.words, Bool.false_eq_true, ↓reduceIte, List.nil_append] at ht
    obtain ⟨q', s', hq, he, hL⟩ := hread s ts rest hT hs hl ht hn hr hE rfl
    have ht' := ht
    simp only [Param.words] at ht'
    obtain ⟨nm, ts', rfl, hnm, h'⟩ := Touching.cons_one (by simpa [identWord] using ht')
    have hs' : s.rest = nm :: (ts' ++ rest) := by simpa using hs
    obtain ⟨y, r', hyr⟩ : ∃ y r', ts' ++ rest = y :: r' := List.exists_cons_of_ne_nil (by simp [hr])
    have hy := hafter ts' h' y (by simp [hyr])
    refine ⟨⟨false, { q' with span := ⟨nm.span.start, s'.lastStop⟩ }⟩, s', ?_, ?_, hL⟩
    · simp only [Parse.parseCtorParam]
      rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.peekAt_rest _ _)]
      have hidx : s.rest[1]?.getD s.eof = y := by simp [hs', hyr]
      rw [hidx, if_neg (by simp [hy]), Parse.pure_bind, Parse.bind_eq hq, Parse.bind_eq (Parse.spanFrom_eq _ _)]
      simp [pure, EStateM.pure, hy]
    · simp only [CtorParam.erase, Param.erase] at he ⊢
      simpa [Param.erase] using he
  | true =>
    simp only [CtorParam.words, ↓reduceIte, List.singleton_append] at ht
    obtain ⟨ro, ts', rfl, hro, h'⟩ := Touching.cons_one (by simpa [identWord] using ht)
    have ht' := h'
    simp only [Param.words] at ht'
    obtain ⟨nm, ts'', rfl, hnm, h''⟩ := Touching.cons_one (by simpa [identWord] using ht')
    have hs' : s.rest = ro :: nm :: (ts'' ++ rest) := by simpa using hs
    have hnb : nm.newlineBefore = false := hn nm (by simp) (by rw [hnm]; simp)
    let s₁ := past s ro (nm :: (ts'' ++ rest))
    have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs']
    obtain ⟨q', s', hq, he, hL⟩ := hread s₁ (nm :: ts'') rest (by simp [s₁, hT]) (by simp [s₁]) hl₁ h'
      (fun y hy => hn y (by simp at hy ⊢; simp [hy])) hr hE rfl
    refine ⟨⟨true, { q' with span := ⟨ro.span.start, s'.lastStop⟩ }⟩, s', ?_, ?_,
      leaves_trans (leaves_advance hs' hl) hL⟩
    · simp only [Parse.parseCtorParam]
      rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.peekAt_rest _ _)]
      have hidx : s.rest[1]?.getD s.eof = nm := by simp [hs']
      rw [hidx, if_pos (by simp [Token.isIdent, Token.isAnyIdent, hro, hnm, hnb]),
        Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq hq,
        Parse.bind_eq (Parse.spanFrom_eq _ _)]
      simp [pure, EStateM.pure, Token.isIdent, Token.isAnyIdent, hro, hnm, hnb]
    · simp only [CtorParam.erase, Param.erase] at he ⊢
      simpa [Param.erase] using he

/-- `( params )` of a constructor, which `listStep` and `parseCtorParam` read. -/
theorem ctorParams_reads {T : Edition} (params : List CtorParam) (hps : ∀ p ∈ params, p.param.wf = true)
    (s : ParseState) (its rest : List Token) (rp : Token) (hT : s.target = T) (hs : s.rest = its ++ rp :: rest)
    (hrp : rp.kind = .punct ")") (hl : s.left = s.rest.length)
    (ht : Touching its (separated "," (params.map CtorParam.words))) (hn : ∀ y ∈ its, NoBreak y) :
    ∃ res s', Parse.iterate (10 * (s.left + 1)) #[] (Parse.listStep ")" (fun _ => pure ()) Parse.parseCtorParam) s =
      .ok res s' ∧ res.toList.map CtorParam.erase = params.map CtorParam.erase ∧ Leaves s s' (rp :: rest) := by
  obtain ⟨res, s', hit, he, hL⟩ := iterate_list (close := ")") (refuse := fun _ => pure ()) (by decide)
    params (10 * (s.left + 1)) #[] s its rest rp (fun p hp => parseCtorParam_reads p (hps p hp))
    (fun p _ => ⟨if p.readonly then .ident "readonly" else .ident p.param.name,
      by cases h : p.readonly <;> simp [CtorParam.words, Param.words, identWord, h],
      by split <;> simp, fun _ _ _ => rfl⟩)
    (by have := length_items ht; have : s.left = its.length + rest.length + 1 := by simp [hl, hs]; omega
        omega) hT hs hrp hl ht hn (listAfter_true params)
  exact ⟨res, s', hit, by simpa using he, hL⟩

/-- `class`, a name, `extends Error`, `{`, at most a constructor on its own
lines, and `}`. -/
theorem parseClass_reads {T : Edition} (start : Pos) (exported : Bool) (sp : Span) (name : String)
    (ctor : Option (List CtorParam × Expr)) (hname : exprName name = true) (hc : ctorWF T ctor = true) :
    ∀ (s : ParseState) (ts cts rest : List Token) (rb : Token), s.rest = ts ++ cts ++ rb :: rest →
      s.target = T → s.left = s.rest.length →
      Touching ts [keywordWord "class", identWord name, keywordWord "extends", identWord "Error", punctWord "{"] →
      Laid cts ((ctorLines ctor).map Prod.snd) → rb.kind = .punct "}" → rest ≠ [] →
      ∃ d' s', Parse.parseClass start exported s = .ok d' s' ∧
        d'.erase = (Decl.errorClass sp exported name ctor).erase ∧ Leaves s s' rest := by
  intro s ts cts rest rb hs hT hl ht hcts hrb hr
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  obtain ⟨ck, ts₁, rfl, hck, h₁⟩ := Touching.cons_one (by simpa [keywordWord] using ht)
  obtain ⟨nm, ts₂, rfl, hnm, h₂⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  obtain ⟨ek, ts₃, rfl, hek, h₃⟩ := Touching.cons_one (by simpa [keywordWord] using h₂)
  obtain ⟨er, ts₄, rfl, her, h₄⟩ := Touching.cons_one (by simpa [identWord] using h₃)
  obtain ⟨lb, ts₅, rfl, hlb, h₅⟩ := Touching.cons_one (by simpa [punctWord] using h₄)
  simp [Touching] at h₅; subst h₅
  have hs' : s.rest = ck :: nm :: ek :: er :: lb :: (cts ++ rb :: rest) := by simpa using hs
  let s₁ := past s ck (nm :: ek :: er :: lb :: (cts ++ rb :: rest))
  let s₂ := past s₁ nm (ek :: er :: lb :: (cts ++ rb :: rest))
  let s₃ := past s₂ ek (er :: lb :: (cts ++ rb :: rest))
  let s₄ := past s₃ er (lb :: (cts ++ rb :: rest))
  let s₅ : ParseState := { s₄ with rest := cts ++ rb :: rest, left := s₄.left - 1, lastStop := lb.span.stop }
  have hl₅ : s₅.left = s₅.rest.length := by simp [s₅, s₄, s₃, s₂, s₁, hl, hs']
  have hT₅ : s₅.target = T := by simp [s₅, s₄, s₃, s₂, s₁, hT]
  have hL₅ : Leaves s s₅ (cts ++ rb :: rest) :=
    leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl (by simp [s₁, hl, hs']))
      (leaves_trans (leaves_advance (s := s₂) rfl (by simp [s₂, s₁, hl, hs']))
        (leaves_trans (leaves_advance (s := s₃) rfl (by simp [s₃, s₂, s₁, hl, hs']))
          (leaves_advance (s := s₄) rfl (by simp [s₄, s₃, s₂, s₁, hl, hs'])))))
  cases ctor with
  | none =>
    simp only [ctorLines, List.map_nil, Laid] at hcts
    subst hcts
    refine ⟨.errorClass ⟨start, rb.span.stop⟩ exported name none,
      { s₅ with rest := rest, left := s₅.left - 1, lastStop := rb.span.stop }, ?_, by simp [Decl.erase],
      leaves_trans hL₅ (leaves_advance (s := s₅) rfl hl₅)⟩
    simp only [Parse.parseClass]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname')]
    rw [Parse.bind_eq (Parse.peek_eq (s := s₂) rfl), if_pos (show ek.isKeyword "extends" = true by simp [Token.isKeyword, hek]),
      Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₂) rfl)),
      Parse.bind_eq (Parse.peek_eq (s := s₃) rfl), if_pos (show er.isIdent "Error" = true by simp [Token.isIdent, her]),
      Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₃) rfl)),
      Parse.bind_eq (Parse.expectPunct_ok (s := s₄) rfl (by simp) hlb)]
    rw [Parse.bind_eq (Parse.peek_eq (s := s₅) rfl), if_pos (show rb.isPunct "}" = true by simp [Token.isPunct, hrb]),
      Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₅) rfl hr)), Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  | some c =>
    obtain ⟨params, message⟩ := c
    simp only [ctorWF, Bool.and_eq_true, List.all_eq_true, Expr.wfParen] at hc
    obtain ⟨hps, hwe, hae⟩ := hc
    simp only [ctorLines, List.map_cons, List.map_nil] at hcts
    obtain ⟨a, b, rfl, ha, hna, _, hb⟩ := Laid.cons hcts
    obtain ⟨b₁, b₂, rfl, hb₁, hnb₁, _, hb₂⟩ := Laid.cons hb
    obtain ⟨hb₂t, _⟩ := Laid.one hb₂
    -- `constructor ( params ) {`
    obtain ⟨ct, a₁, rfl, hct, ha₁⟩ := Touching.cons_one (by simpa [identWord] using ha)
    obtain ⟨pts, a₂, rfl, hpts, ha₂⟩ := Touching.append_split ha₁
    obtain ⟨lp, its, rp, rfl, hlp, hits, hrp⟩ := Touching.enclosed (by simpa [enclose] using hpts)
    obtain ⟨cb, a₃, rfl, hcb, ha₃⟩ := Touching.cons_one (by simpa [punctWord] using ha₂)
    simp [Touching] at ha₃; subst ha₃
    -- `super ( message ) ;`
    obtain ⟨sk, b₁', rfl, hsk, hb₁'⟩ := Touching.cons_one (by simpa [keywordWord] using hb₁)
    obtain ⟨lpm, b₁'', rfl, hlpm, hb₁''⟩ := Touching.cons_one (by simpa [punctWord] using hb₁')
    obtain ⟨mts, b₁''', rfl, hmts, hb₁'''⟩ := Touching.append_split hb₁''
    obtain ⟨rpm, b₁'''', rfl, hrpm, hb₁''''⟩ := Touching.cons_one (by simpa [punctWord] using hb₁''')
    obtain ⟨semi, b₁''''', rfl, hsemi, hb₁'''''⟩ := Touching.cons_one (by simpa [punctWord] using hb₁'''')
    simp [Touching] at hb₁'''''; subst hb₁'''''
    -- `}` of the constructor
    obtain ⟨cr, b₂', rfl, hcr, hb₂'⟩ := Touching.cons_one (by simpa [punctWord] using hb₂t)
    simp [Touching] at hb₂'; subst hb₂'
    have hs₅ : s₅.rest = ct :: lp :: (its ++ rp :: cb :: sk :: lpm :: (mts ++ rpm :: semi :: cr :: rb :: rest)) := by
      simp [s₅]
    let s₆ := past s₅ ct (lp :: (its ++ rp :: cb :: sk :: lpm :: (mts ++ rpm :: semi :: cr :: rb :: rest)))
    let s₇ : ParseState := { s₆ with rest := its ++ rp :: cb :: sk :: lpm :: (mts ++ rpm :: semi :: cr :: rb :: rest), left := s₆.left - 1, lastStop := lp.span.stop }
    have hl₇ : s₇.left = s₇.rest.length := by simp [s₇, s₆, hl₅, hs₅]
    have hT₇ : s₇.target = T := by simp [s₇, s₆, hT₅]
    obtain ⟨res, s₈, hit, hes, hL₈⟩ := ctorParams_reads params hps s₇ its
      (cb :: sk :: lpm :: (mts ++ rpm :: semi :: cr :: rb :: rest)) rp hT₇ rfl hrp hl₇ hits
      (fun y hy => hna y (by simp [hy]))
    have hs₈ : s₈.rest = rp :: cb :: sk :: lpm :: (mts ++ rpm :: semi :: cr :: rb :: rest) := hL₈.rest_eq
    let s₉ : ParseState := { s₈ with rest := cb :: sk :: lpm :: (mts ++ rpm :: semi :: cr :: rb :: rest), left := s₈.left - 1, lastStop := rp.span.stop }
    let s₁₀ : ParseState := { s₉ with rest := sk :: lpm :: (mts ++ rpm :: semi :: cr :: rb :: rest), left := s₉.left - 1, lastStop := cb.span.stop }
    let s₁₁ := past s₁₀ sk (lpm :: (mts ++ rpm :: semi :: cr :: rb :: rest))
    let s₁₂ : ParseState := { s₁₁ with rest := mts ++ rpm :: semi :: cr :: rb :: rest, left := s₁₁.left - 1, lastStop := lpm.span.stop }
    have hl₁₂ : s₁₂.left = s₁₂.rest.length := by simp [s₁₂, s₁₁, s₁₀, s₉, hL₈.left_eq]
    have hT₁₂ : s₁₂.target = T := by simp [s₁₂, s₁₁, s₁₀, s₉, hL₈.target_eq, hT₇]
    obtain ⟨m', s₁₃, hpm, hem, hL₁₃⟩ := parseExpression_budget message hwe s₁₂ mts (rpm :: semi :: cr :: rb :: rest)
      hT₁₂ (by simp [s₁₂]) hl₁₂ hmts (fun y hy => hnb₁ y (by
        simp only [List.tail_cons]; exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_of_mem_tail hy)))) (by simp)
      (EndsExpr.closer hrpm) (by simpa [hrpm] using afterOK_closer hae _)
    have hs₁₃ : s₁₃.rest = rpm :: semi :: cr :: rb :: rest := hL₁₃.rest_eq
    let s₁₄ : ParseState := { s₁₃ with rest := semi :: cr :: rb :: rest, left := s₁₃.left - 1, lastStop := rpm.span.stop }
    let s₁₅ : ParseState := { s₁₄ with rest := cr :: rb :: rest, left := s₁₄.left - 1, lastStop := semi.span.stop }
    let s₁₆ := past s₁₅ cr (rb :: rest)
    refine ⟨.errorClass ⟨start, rb.span.stop⟩ exported name (some (res.toList, m')),
      { s₁₆ with rest := rest, left := s₁₆.left - 1, lastStop := rb.span.stop }, ?_, ?_, ?_⟩
    · simp only [Parse.parseClass]
      rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs')), Parse.bind_eq (readName_ok (s := s₁) rfl hnm hname')]
      rw [Parse.bind_eq (Parse.peek_eq (s := s₂) rfl), if_pos (show ek.isKeyword "extends" = true by simp [Token.isKeyword, hek]),
        Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₂) rfl)),
        Parse.bind_eq (Parse.peek_eq (s := s₃) rfl), if_pos (show er.isIdent "Error" = true by simp [Token.isIdent, her]),
        Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₃) rfl)),
        Parse.bind_eq (Parse.expectPunct_ok (s := s₄) rfl (by simp) hlb)]
      rw [Parse.bind_eq (Parse.peek_eq hs₅), if_neg (show ¬ (ct.isPunct "}" = true) by simp [Token.isPunct, hct]),
        Parse.pure_bind, if_pos (show ct.isIdent "constructor" = true by simp [Token.isIdent, hct]), Parse.pure_bind,
        Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs₅)),
        Parse.bind_eq (Parse.expectPunct_ok (s := s₆) rfl (by simp) hlp), Parse.bind_eq (Parse.budget_eq _),
        Parse.bind_eq hit, Parse.bind_eq (Parse.expectPunct_ok hs₈ (by simp) hrp),
        Parse.bind_eq (Parse.expectPunct_ok (s := s₉) rfl (by simp) hcb),
        Parse.bind_eq (Parse.peek_eq (s := s₁₀) rfl), if_pos (show sk.isKeyword "super" = true by simp [Token.isKeyword, hsk]),
        Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₁₀) rfl)),
        Parse.bind_eq (Parse.expectPunct_ok (s := s₁₁) rfl (by simp) hlpm), Parse.bind_eq (Parse.budget_eq _),
        Parse.bind_eq hpm, Parse.bind_eq (Parse.expectPunct_ok hs₁₃ (by simp) hrpm),
        Parse.bind_eq (endStatement_semi (s := s₁₄) rfl (by simp) hsemi),
        Parse.bind_eq (Parse.peek_eq (s := s₁₅) rfl), if_pos (show cr.isPunct "}" = true by simp [Token.isPunct, hcr]),
        Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (Parse.advance_eq (s := s₁₅) rfl)),
        Parse.bind_eq (Parse.expectPunct_ok (s := s₁₆) rfl hr hrb), Parse.bind_eq (Parse.spanFrom_eq _ _)]
      rfl
    · simp [Decl.erase, hes, hem]
    · have L1 := leaves_trans hL₅ (leaves_advance hs₅ hl₅)
      have L2 := leaves_trans L1 (leaves_advance (s := s₆) rfl (by simp [s₆, hl₅, hs₅]))
      have L3 := leaves_trans L2 hL₈
      have L4 := leaves_trans L3 (leaves_advance hs₈ (by rw [hL₈.left_eq, hs₈]))
      have L5 := leaves_trans L4 (leaves_advance (s := s₉) rfl (by simp [s₉, hL₈.left_eq]))
      have L6 := leaves_trans L5 (leaves_advance (s := s₁₀) rfl (by simp [s₁₀, s₉, hL₈.left_eq]))
      have L7 := leaves_trans L6 (leaves_advance (s := s₁₁) rfl (by simp [s₁₁, s₁₀, s₉, hL₈.left_eq]))
      have L8 := leaves_trans L7 hL₁₃
      have L9 := leaves_trans L8 (leaves_advance hs₁₃ (by rw [hL₁₃.left_eq, hs₁₃]))
      have L10 := leaves_trans L9 (leaves_advance (s := s₁₄) rfl (by simp [s₁₄, hL₁₃.left_eq]))
      have L11 := leaves_trans L10 (leaves_advance (s := s₁₅) rfl (by simp [s₁₅, s₁₄, hL₁₃.left_eq]))
      exact leaves_trans L11 (leaves_advance (s := s₁₆) rfl (by simp [s₁₆, s₁₅, s₁₄, hL₁₃.left_eq]))

/-- `class Name extends Error { … }`, with at most a constructor. -/
theorem parseDecl_class {T : Edition} (sp : Span) (exported : Bool) (name : String)
    (ctor : Option (List CtorParam × Expr)) (hw : (Decl.errorClass sp exported name ctor).wf T = true) :
    ReadsD T Parse.parseDecl (.errorClass sp exported name ctor) := by
  intro s ts rest _ _ hs hl ht hr _
  simp only [Decl.wf, Bool.and_eq_true] at hw
  obtain ⟨hname, hc⟩ := hw
  simp only [Decl.wordLines, Decl.lines, List.map_cons, List.map_append, List.map_nil] at ht
  obtain ⟨a, b, rfl, ha, _, _, hb⟩ := Laid.cons ht
  obtain ⟨cts, b₂, rfl, hcts, hb₂, _⟩ := Laid.append (l₁ := (ctorLines ctor).map Prod.snd) hb
  obtain ⟨hrb, _⟩ := Laid.one hb₂
  obtain ⟨rb, b₂', rfl, hrbk, h'⟩ := Touching.cons_one (by simpa [punctWord] using hrb)
  simp [Touching] at h'; subst h'
  cases exported with
  | false =>
    simp only [exportWords, Bool.false_eq_true, ↓reduceIte, List.nil_append] at ha
    obtain ⟨ck, a₁, rfl, hck, h₁⟩ := Touching.cons_one (by simpa [keywordWord] using ha)
    obtain ⟨nm, a₂, rfl, _, _⟩ := Touching.cons_one (by simpa [identWord] using h₁)
    have hs' : s.rest = ck :: nm :: (a₂ ++ (cts ++ rb :: rest)) := by simpa using hs
    obtain ⟨d', s', hp, he, hL⟩ := parseClass_reads ck.span.start (ck.isKeyword "export") sp name ctor hname hc
      s (ck :: nm :: a₂) cts rest rb (by simpa using hs) (by assumption) hl ha hcts hrbk hr
    refine ⟨d', s', ?_, by rw [he]; simp [Decl.erase, Token.isKeyword, hck], hL⟩
    rw [parseDecl_body hs' (by simp) (by rw [hck]; simp) (fun h => by simp [Token.isKeyword, hck] at h),
      if_neg (show ¬ (ck.isKeyword "export" = true) by simp [Token.isKeyword, hck]),
      parseDeclBody_class _ _ hs' hck]
    exact hp
  | true =>
    simp only [exportWords, ↓reduceIte, List.singleton_append] at ha
    obtain ⟨ex, a₀, rfl, hex, h₀⟩ := Touching.cons_one (by simpa [keywordWord] using ha)
    obtain ⟨ck, a₁, rfl, hck, h₁⟩ := Touching.cons_one (by simpa [keywordWord] using h₀)
    obtain ⟨nm, a₂, rfl, _, _⟩ := Touching.cons_one (by simpa [identWord] using h₁)
    have hs' : s.rest = ex :: ck :: nm :: (a₂ ++ (cts ++ rb :: rest)) := by simpa using hs
    let s₁ := past s ex (ck :: (nm :: (a₂ ++ (cts ++ rb :: rest))))
    obtain ⟨d', s', hp, he, hL⟩ := parseClass_reads ex.span.start (ex.isKeyword "export") sp name ctor hname hc
      s₁ (ck :: nm :: a₂) cts rest rb (by simp [s₁]) (by simp [s₁]; assumption) (by simp [s₁, hl, hs']) h₀ hcts hrbk hr
    refine ⟨d', s', ?_, by rw [he]; simp [Decl.erase, Token.isKeyword, hex], leaves_trans (leaves_advance hs' hl) hL⟩
    rw [parseDecl_body hs' (by simp) (by rw [hex]; simp) (fun _ => startsExportList_head rfl (by rw [hck]; simp) (by rw [hck]; simp)),
      if_pos (show ex.isKeyword "export" = true by simp [Token.isKeyword, hex]),
      parseDeclBody_class (s := s₁) _ _ rfl hck]
    exact hp

theorem parseDecl_enum {T : Edition} (sp : Span) (exported : Bool) (name : String) (members : List EnumMember)
    (hw : (Decl.enum sp exported name members).wf T = true) :
    ReadsD T Parse.parseDecl (.enum sp exported name members) := by
  intro s ts rest _ _ hs hl ht hr _
  simp only [Decl.wf] at hw
  simp only [Decl.wordLines, Decl.lines, List.map_cons, List.map_append, List.map_map, List.map_nil] at ht
  obtain ⟨a, b, rfl, ha, _, _, hb⟩ := Laid.cons ht
  obtain ⟨mts, b₂, rfl, hmts, hb₂, _⟩ :=
    Laid.append (l₁ := members.map EnumMember.words) (by simpa [Function.comp_def] using hb)
  obtain ⟨hrb, _⟩ := Laid.one hb₂
  obtain ⟨rb, b₂', rfl, hrbk, h'⟩ := Touching.cons_one (by simpa [punctWord] using hrb)
  simp [Touching] at h'; subst h'
  cases exported with
  | false =>
    simp only [exportWords, Bool.false_eq_true, ↓reduceIte, List.nil_append] at ha
    obtain ⟨ek, a₁, rfl, hek, h₁⟩ := Touching.cons_one (by simpa [keywordWord] using ha)
    obtain ⟨nm, a₂, rfl, _, _⟩ := Touching.cons_one (by simpa [identWord] using h₁)
    have hs' : s.rest = ek :: nm :: (a₂ ++ (mts ++ rb :: rest)) := by simpa using hs
    obtain ⟨d', s', hp, he, hL⟩ := parseEnum_reads ek.span.start (ek.isKeyword "export") sp name members hw
      s (ek :: nm :: a₂) mts rest rb (by simpa using hs) hl ha hmts hrbk hr
    refine ⟨d', s', ?_, by rw [he]; simp [Decl.erase, Token.isKeyword, hek], hL⟩
    rw [parseDecl_body hs' (by simp) (by rw [hek]; simp) (fun h => by simp [Token.isKeyword, hek] at h),
      if_neg (show ¬ (ek.isKeyword "export" = true) by simp [Token.isKeyword, hek]),
      parseDeclBody_enum _ _ hs' hek]
    exact hp
  | true =>
    simp only [exportWords, ↓reduceIte, List.singleton_append] at ha
    obtain ⟨ex, a₀, rfl, hex, h₀⟩ := Touching.cons_one (by simpa [keywordWord] using ha)
    obtain ⟨ek, a₁, rfl, hek, h₁⟩ := Touching.cons_one (by simpa [keywordWord] using h₀)
    obtain ⟨nm, a₂, rfl, _, _⟩ := Touching.cons_one (by simpa [identWord] using h₁)
    have hs' : s.rest = ex :: ek :: nm :: (a₂ ++ (mts ++ rb :: rest)) := by simpa using hs
    let s₁ := past s ex (ek :: (nm :: (a₂ ++ (mts ++ rb :: rest))))
    obtain ⟨d', s', hp, he, hL⟩ := parseEnum_reads ex.span.start (ex.isKeyword "export") sp name members hw
      s₁ (ek :: nm :: a₂) mts rest rb (by simp [s₁]) (by simp [s₁, hl, hs']) h₀ hmts hrbk hr
    refine ⟨d', s', ?_, by rw [he]; simp [Decl.erase, Token.isKeyword, hex], leaves_trans (leaves_advance hs' hl) hL⟩
    rw [parseDecl_body hs' (by simp) (by rw [hex]; simp) (fun _ => startsExportList_head rfl (by rw [hek]; simp) (by rw [hek]; simp)),
      if_pos (show ex.isKeyword "export" = true by simp [Token.isKeyword, hex]),
      parseDeclBody_enum (s := s₁) _ _ rfl hek]
    exact hp


theorem parseDecl_function {T : Edition} (sp : Span) (exported : Bool) (name : String) (tps : List String)
    (params : List Param) (rt : Option TypeExpr) (body : Stmt)
    (hw : (Decl.function sp exported name tps params rt body).wf T = true) :
    ReadsD T Parse.parseDecl (.function sp exported name tps params rt body) := by
  intro s ts rest hT hF hs hl ht hr _
  simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨hname, htps⟩, hps⟩, hrt⟩, hblk⟩, hbw⟩ := hw
  obtain ⟨bsp, bs, rfl⟩ : ∃ bsp bs, body = .block bsp bs := by
    cases body <;> simp [Stmt.isBlock] at hblk; exact ⟨_, _, rfl⟩
  have hrt' : ∀ t ∈ rt, t.wf = true := by
    intro t ht; cases rt with
    | none => cases ht
    | some t' => simp at ht; subst ht; simpa using hrt
  simp only [Decl.wordLines, Decl.lines, List.map_cons] at ht
  obtain ⟨a, b, rfl, ha, hna, _, hb⟩ := Laid.cons ht
  cases exported with
  | false =>
    simp only [exportWords, Bool.false_eq_true, ↓reduceIte, List.nil_append] at ha
    obtain ⟨fk, a₁, rfl, hfk, _⟩ := Touching.cons_one (by simpa [keywordWord] using ha)
    have hs' : s.rest = fk :: (a₁ ++ (b ++ rest)) := by simpa using hs
    obtain ⟨d', s', hp, he, hL⟩ := parseFunction_reads fk.span.start (fk.isKeyword "export") sp name tps params rt bsp bs
      hname htps hps hrt' hbw s (fk :: a₁) b rest hT hF (by simpa using hs) hl ha hna hb hr
    refine ⟨d', s', ?_, by rw [he]; simp [Decl.erase, Token.isKeyword, hfk], hL⟩
    rw [parseDecl_body hs' (by simp [hr]) (by rw [hfk]; simp) (fun h => by simp [Token.isKeyword, hfk] at h),
      if_neg (show ¬ (fk.isKeyword "export" = true) by simp [Token.isKeyword, hfk]),
      parseDeclBody_function _ _ hs' hfk]
    exact hp
  | true =>
    simp only [exportWords, ↓reduceIte, List.singleton_append] at ha
    obtain ⟨ex, a₀, rfl, hex, h₀⟩ := Touching.cons_one (by simpa [keywordWord] using ha)
    obtain ⟨fk, a₁, rfl, hfk, _⟩ := Touching.cons_one (by simpa [keywordWord] using h₀)
    have hs' : s.rest = ex :: fk :: (a₁ ++ (b ++ rest)) := by simpa using hs
    let s₁ := past s ex (fk :: (a₁ ++ (b ++ rest)))
    obtain ⟨d', s', hp, he, hL⟩ := parseFunction_reads ex.span.start (ex.isKeyword "export") sp name tps params rt bsp bs
      hname htps hps hrt' hbw s₁ (fk :: a₁) b rest hT hF (by simp [s₁]) (by simp [s₁, hl, hs'])
      (by simpa [keywordWord] using h₀)
      (fun y hy => hna y (by simp at hy ⊢; simp [hy])) hb hr
    refine ⟨d', s', ?_, by rw [he]; simp [Decl.erase, Token.isKeyword, hex], leaves_trans (leaves_advance hs' hl) hL⟩
    rw [parseDecl_body hs' (by simp) (by rw [hex]; simp) (fun _ => startsExportList_head rfl (by rw [hfk]; simp) (by rw [hfk]; simp)),
      if_pos (show ex.isKeyword "export" = true by simp [Token.isKeyword, hex]),
      parseDeclBody_function (s := s₁) _ _ rfl hfk]
    exact hp

theorem parseDecl_exportedVar {T : Edition} (sp : Span) (d : VarDecl)
    (hw : (Decl.exportedVar sp d).wf T = true) :
    ReadsD T Parse.parseDecl (.exportedVar sp d) := by
  intro s ts rest hT _ hs hl ht hr _
  simp only [Decl.wf] at hw
  simp only [Decl.wordLines, Decl.lines, List.map_cons, List.map_nil] at ht
  obtain ⟨h1, hnl⟩ := Laid.one ht
  obtain ⟨ex, ts₀, rfl, hex, h₀⟩ := Touching.cons_one (by simpa [keywordWord] using h1)
  have h₀' := h₀
  simp only [VarDecl.words, VarKind.word_eq] at h₀'
  obtain ⟨kw, ts₁, rfl, hkw, h₁⟩ := Touching.cons_one (by simpa using h₀')
  obtain ⟨nm, ts₂, rfl, hnm, _⟩ := Touching.cons_one (by simpa [identWord] using h₁)
  have hs' : s.rest = ex :: kw :: nm :: (ts₂ ++ rest) := by simpa using hs
  let s₁ := past s ex (kw :: (nm :: (ts₂ ++ rest)))
  obtain ⟨d', s', hp, he, hL⟩ := parseVarDecl_reads d hw s₁ (kw :: nm :: ts₂) rest hT (by simp [s₁])
    (by simp [s₁, hl, hs']) h₀ (fun y hy => hnl y (by simp at hy ⊢; simp [hy])) hr
  refine ⟨.exportedVar ⟨ex.span.start, s'.lastStop⟩ d', s', ?_, by simp [Decl.erase, he],
    leaves_trans (leaves_advance hs' hl) hL⟩
  rw [parseDecl_body hs' (by simp) (by rw [hex]; simp) (fun _ => startsExportList_head rfl (by cases hk : d.kind <;> rw [hk] at hkw <;> simp [VarKind.token] at hkw <;> rw [hkw] <;> simp)
      (by cases hk : d.kind <;> rw [hk] at hkw <;> simp [VarKind.token] at hkw <;> rw [hkw] <;> simp)),
    if_pos (show ex.isKeyword "export" = true by simp [Token.isKeyword, hex])]
  simp only [Parse.parseDeclBody]
  rw [Parse.bind_eq (Parse.peek_eq (s := s₁) rfl), Parse.bind_eq (Parse.peekAt_rest _ _)]
  cases hk : d.kind <;> rw [hk] at hkw <;> simp only [VarKind.token] at hkw
  all_goals
    rw [if_neg (show ¬ (kw.isKeyword "function" = true) by simp [Token.isKeyword, hkw])]
    rw [if_neg (show ¬ ((kw.isIdent "interface" && _) = true) by simp [Token.isIdent, hkw])]
    rw [if_neg (show ¬ ((kw.isIdent "type" && _) = true) by simp [Token.isIdent, hkw])]
    rw [if_neg (show ¬ (kw.isKeyword "enum" = true) by simp [Token.isKeyword, hkw])]
    rw [if_neg (show ¬ (kw.isKeyword "class" = true) by simp [Token.isKeyword, hkw])]
    rw [if_pos (show ex.isKeyword "export" = true by simp [Token.isKeyword, hex])]
    rw [if_pos (show (kw.isKeyword "const" || kw.isIdent "let") = true by simp [Token.isKeyword, Token.isIdent, hkw]),
      Parse.pure_bind, Parse.bind_eq hp, Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl


/-- Every well-formed declaration. -/
theorem parseDecl_reads {T : Edition} (d : Decl) (hw : d.wf T = true) : ReadsD T Parse.parseDecl d := by
  cases d with
  | «import» sp names source => exact parseDecl_import sp names source hw
  | exports sp names source => exact parseDecl_exports sp names source hw
  | function sp e n tps ps rt b => exact parseDecl_function sp e n tps ps rt b hw
  | interface sp e n tps fs => exact parseDecl_interface sp e n tps fs hw
  | typeAlias sp e n tps t => exact parseDecl_typeAlias sp e n tps t hw
  | enum sp e n ms => exact parseDecl_enum sp e n ms hw
  | errorClass sp e n ctor => exact parseDecl_class sp e n ctor hw
  | exportedVar sp d => exact parseDecl_exportedVar sp d hw
  | stmt st => exact parseDecl_stmt st hw

/-! ### Modules -/

def Module.wf (T : Edition) (m : Module) : Bool := m.decls.all (Decl.wf T)

/-- A declaration starts with a token that is not the end of the file and not `else`. -/
theorem Decl.first {T : Edition} (d : Decl) (hw : d.wf T = true) {ts : List Token} (h : Laid ts d.wordLines) :
    ∃ x ts', ts = x :: ts' ∧ x.kind ≠ .eof ∧ x.kind ≠ .keyword "else" := by
  cases d with
  | stmt st =>
    obtain ⟨x, ts', rfl, hx⟩ := Laid.first (st := st) hw (by simpa [Decl.wordLines, Decl.lines, Stmt.wordLines] using h)
    exact ⟨x, ts', rfl, hx.2.1, hx.2.2.1⟩
  | «import» sp names source =>
    have hk := h.kinds
    cases ts with
    | nil => simp [Decl.wordLines, Decl.lines, keywordWord, identWord] at hk
    | cons x ts' => refine ⟨x, ts', rfl, ?_⟩; simp [Decl.wordLines, Decl.lines, keywordWord, identWord] at hk; rw [hk.1]; simp
  | exports sp names source =>
    have hk := h.kinds
    cases ts with
    | nil => simp [Decl.wordLines, Decl.lines, keywordWord] at hk
    | cons x ts' => refine ⟨x, ts', rfl, ?_⟩; simp [Decl.wordLines, Decl.lines, keywordWord] at hk; rw [hk.1]; simp
  | function sp e n tps ps rt b =>
    have hk := h.kinds
    cases ts with
    | nil => cases e <;> simp [Decl.wordLines, Decl.lines, exportWords, keywordWord, identWord] at hk
    | cons x ts' => refine ⟨x, ts', rfl, ?_⟩; cases e <;> simp [Decl.wordLines, Decl.lines, exportWords, keywordWord, identWord] at hk <;> rw [hk.1] <;> simp
  | interface sp e n tps fs =>
    have hk := h.kinds
    cases ts with
    | nil => cases e <;> simp [Decl.wordLines, Decl.lines, exportWords, keywordWord, identWord] at hk
    | cons x ts' => refine ⟨x, ts', rfl, ?_⟩; cases e <;> simp [Decl.wordLines, Decl.lines, exportWords, keywordWord, identWord] at hk <;> rw [hk.1] <;> simp
  | typeAlias sp e n tps t =>
    have hk := h.kinds
    cases ts with
    | nil => cases e <;> simp [Decl.wordLines, Decl.lines, exportWords, keywordWord, identWord] at hk
    | cons x ts' => refine ⟨x, ts', rfl, ?_⟩; cases e <;> simp [Decl.wordLines, Decl.lines, exportWords, keywordWord, identWord] at hk <;> rw [hk.1] <;> simp
  | enum sp e n ms =>
    have hk := h.kinds
    cases ts with
    | nil => cases e <;> simp [Decl.wordLines, Decl.lines, exportWords, keywordWord, identWord] at hk
    | cons x ts' => refine ⟨x, ts', rfl, ?_⟩; cases e <;> simp [Decl.wordLines, Decl.lines, exportWords, keywordWord, identWord] at hk <;> rw [hk.1] <;> simp
  | errorClass sp e n ctor =>
    have hk := h.kinds
    cases ts with
    | nil => cases e <;> simp [Decl.wordLines, Decl.lines, exportWords, keywordWord, identWord] at hk
    | cons x ts' => refine ⟨x, ts', rfl, ?_⟩; cases e <;> simp [Decl.wordLines, Decl.lines, exportWords, keywordWord, identWord] at hk <;> rw [hk.1] <;> simp
  | exportedVar sp d =>
    have hk := h.kinds
    cases ts with
    | nil => simp [Decl.wordLines, Decl.lines, keywordWord] at hk
    | cons x ts' => refine ⟨x, ts', rfl, ?_⟩; simp [Decl.wordLines, Decl.lines, keywordWord] at hk; rw [hk.1]; simp


theorem Module.lines_words (m : Module) : m.lines.map Prod.snd = (m.decls.map Decl.wordLines).flatten := by
  obtain ⟨decls⟩ := m
  simp only [Module.lines]
  induction decls with
  | nil => rfl
  | cons d ds ih => simp [List.flatMap_cons, ih, Decl.wordLines]

theorem Laid.length_decls {T : Edition} : ∀ {decls : List Decl} {ts : List Token}, (∀ d ∈ decls, d.wf T = true) →
    Laid ts (decls.map Decl.wordLines).flatten → decls.length ≤ ts.length
  | [], _, _, _ => by simp
  | d :: decls, ts, hw, h => by
    obtain ⟨a, b, rfl, ha, hb, _⟩ := Laid.append (by simpa using h)
    obtain ⟨x, a', rfl, _⟩ := Decl.first d (hw d (by simp)) ha
    have := Laid.length_decls (fun e he => hw e (by simp [he])) hb
    simp; omega

/-- The loop of `parseModule` reads the declarations of a module, which the end of the file follows. -/
theorem decl_loop {T : Edition} :
    ∀ (decls : List Decl) (fuel : Nat) (acc : Array Decl) (s : ParseState) (ts : List Token) (c : Token),
      (∀ d ∈ decls, d.wf T = true) → decls.length < fuel → s.target = T → s.inFunction = false →
      s.rest = ts ++ [c] → c.kind = .eof → s.left = s.rest.length →
      Laid ts (decls.map Decl.wordLines).flatten →
      ∃ res s', Parse.iterate fuel acc Parse.declStep s = .ok res s' ∧
        res.toList.map Decl.erase = (acc.toList ++ decls).map Decl.erase ∧ Leaves s s' [c] := by
  intro decls
  induction decls with
  | nil =>
    intro fuel acc s ts c _ hlen _ _ hs hc hl ht
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    simp [Laid] at ht; subst ht
    have hs' : s.rest = [c] := by simpa using hs
    refine ⟨acc, s, Parse.iterate_false ?_, by simp, Leaves.refl hs' (by simp [hl, hs'])⟩
    simp only [Parse.declStep]
    rw [Parse.bind_eq (Parse.peek_eq hs')]
    simp [Token.isEof, hc, pure, EStateM.pure]
  | cons d decls ih =>
    intro fuel acc s ts c hw hlen hT hF hs hc hl ht
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    obtain ⟨a, b, rfl, ha, hb, _⟩ := Laid.append (by simpa using ht)
    obtain ⟨x, a', rfl, hx1, _⟩ := Decl.first d (hw d (by simp)) ha
    have hs' : s.rest = x :: (a' ++ (b ++ [c])) := by simpa using hs
    have hnext : ∀ u ∈ (b ++ [c]).head?, u.kind ≠ .keyword "else" := by
      cases decls with
      | nil =>
        simp [Laid] at hb; subst hb
        intro u hu; simp at hu; subst hu; rw [hc]; simp
      | cons d' ds =>
        obtain ⟨a₂, b₂, rfl, ha₂, _, _⟩ := Laid.append (by simpa using hb)
        obtain ⟨y, a₂', rfl, _, hy⟩ := Decl.first d' (hw d' (by simp)) ha₂
        intro u hu; simp at hu; subst hu; exact hy
    obtain ⟨d', s₁, hp, he, hL₁⟩ := parseDecl_reads d (hw d (by simp)) s (x :: a') (b ++ [c]) hT hF
      (by simp [hs']) hl ha (by simp) (fun _ => hnext)
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL₁.left_eq, hL₁.rest_eq]
    obtain ⟨res, s', hit, he', hL'⟩ := ih f' (acc.push d') s₁ b c (fun e he => hw e (by simp [he]))
      (by simp at hlen; omega) (hL₁.target_eq.trans hT) (hL₁.inFunction_eq.trans hF) hL₁.rest_eq hc hl₁ hb
    refine ⟨res, s', ?_, by rw [he']; simp [he], leaves_trans hL₁ hL'⟩
    rw [Parse.iterate_true (acc' := acc.push d') (s' := s₁)]
    · exact hit
    · simp only [Parse.declStep]
      rw [Parse.bind_eq (Parse.peek_eq hs')]
      rw [if_neg (show ¬ (x.isEof = true) by simp [Token.isEof, hx1]), Parse.pure_bind, Parse.bind_eq hp]
      rfl

/-- The parser's round trip for a module, on tokens: `parseModule` reads the
tokens of the printed lines of every well-formed module, which the end of the
file follows, as that module apart from spans. -/
theorem module_reads {T : Edition} (m : Module) (hm : m.wf T = true) :
    ∀ (s : ParseState) (ts : List Token) (c : Token), s.target = T → s.inFunction = false →
      s.rest = ts ++ [c] → c.kind = .eof → s.left = s.rest.length → Laid ts (m.lines.map Prod.snd) →
      ∃ m' s', Parse.parseModule s = .ok m' s' ∧ m'.erase = m.erase := by
  intro s ts c hT hF hs hc hl ht
  rw [Module.lines_words] at ht
  have hw : ∀ d ∈ m.decls, d.wf T = true := by simpa [Module.wf] using hm
  have hlen := Laid.length_decls hw ht
  obtain ⟨res, s', hit, he, _⟩ := decl_loop m.decls (10 * (s.left + 1)) #[] s ts c hw
    (by have : s.left = ts.length + 1 := by simp [hl, hs]
        omega) hT hF hs hc hl ht
  refine ⟨{ decls := res.toList }, s', ?_, by simpa [Module.erase] using he⟩
  simp only [Parse.parseModule]
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hit]
  rfl

end tolean.TypeScript.Syntax
