import tolean.TypeScript.Syntax.RoundTripLex
import tolean.TypeScript.Syntax.ParseWF

/-!
The parser's round trip on source text: for every module that the parser
gives, the parser reads the printed source as the same module, apart from
spans (`parseChars_reads`).

Three results meet here. `parseTokens_wf` (`Syntax/ParseWF.lean`) states
that the module is well formed, and that every word it prints is one that the
lexer gives back (`Word.ok`). `lexChars_render` (`Syntax/RoundTripLex.lean`)
states that the lexer reads the printed lines as tokens that `Laid`
describes. And `module_reads` (`Syntax/RoundTripDecl.lean`) states that the
parser reads those tokens as the module. `lexChars_render` asks two things of
the printed words: each one lexes back, and each line break inside a line
comes before a `(` (`breaksOK`). This file proves the second for every
module, from the printer alone.
-/
namespace tolean.TypeScript.Syntax

open tolean

set_option linter.unusedSimpArgs false

theorem breaksOK_append : ∀ (a b : List Word), breaksOK a = true → breaksOK b = true →
    (a.getLast? = some [] → b.head? = some [.punct "("]) → breaksOK (a ++ b) = true
  | [], b, _, hb, _ => by simpa using hb
  | [] :: a, b, ha, hb, hl => by
    simp only [breaksOK, Bool.and_eq_true, beq_iff_eq] at ha
    simp only [List.cons_append, breaksOK, Bool.and_eq_true, beq_iff_eq]
    refine ⟨?_, breaksOK_append a b ha.2 hb (fun h => hl (by cases a <;> simp_all))⟩
    cases a with
    | nil => simpa using hl (by simp)
    | cons w a => simpa using ha.1
  | (k :: w) :: a, b, ha, hb, hl => by
    simp only [breaksOK] at ha
    simp only [List.cons_append, breaksOK]
    exact breaksOK_append a b ha hb (fun h => hl (by cases a <;> simp_all))

/-- Words with no `lineBreak`. -/
theorem breaksOK_of_ne : ∀ ws : List Word, (∀ w ∈ ws, w ≠ []) → breaksOK ws = true
  | [], _ => rfl
  | [] :: _, h => absurd rfl (h [] (by simp))
  | (k :: w) :: ws, h => by simp only [breaksOK]; exact breaksOK_of_ne ws (fun x hx => h x (by simp [hx]))

/-- Words that `breaksOK` accepts, that are not empty and end with a word that has tokens. -/
def Fine (ws : List Word) : Prop := breaksOK ws = true ∧ ws.getLast? ≠ some [] ∧ ws ≠ []

theorem getLast?_append_ne {a b : List Word} (hb : b ≠ []) : (a ++ b).getLast? = b.getLast? := by
  cases b with
  | nil => exact absurd rfl hb
  | cons y b =>
    rw [List.getLast?_append]
    cases h : (y :: b).getLast? with
    | none => simp at h
    | some z => rfl

theorem Fine.append {a b : List Word} (ha : Fine a) (hb : Fine b) : Fine (a ++ b) :=
  ⟨breaksOK_append a b ha.1 hb.1 (fun h => absurd h ha.2.1),
    by rw [getLast?_append_ne hb.2.2]; exact hb.2.1, by simp [ha.2.2]⟩

theorem Fine.word {w : Word} (hw : w ≠ []) : Fine [w] := ⟨breaksOK_of_ne _ (by simpa using hw), by simpa using hw, by simp⟩

theorem Fine.cons {w : Word} {ws : List Word} (hw : w ≠ []) (h : Fine ws) : Fine (w :: ws) := by
  simpa using (Fine.word hw).append h

theorem fine_separated (sep : String) : ∀ items : List (List Word), (∀ x ∈ items, Fine x) →
    breaksOK (separated sep items) = true ∧ (separated sep items).getLast? ≠ some []
  | [], _ => ⟨rfl, by simp [separated]⟩
  | [x], h => by have := h x (by simp); exact ⟨this.1, this.2.1⟩
  | x :: y :: rest, h => by
    have hx := h x (by simp)
    have hr := fine_separated sep (y :: rest) (fun z hz => h z (by simp_all))
    have hyr : separated sep (y :: rest) ≠ [] := by
      cases rest with
      | nil => simpa [separated] using (h y (by simp)).2.2
      | cons z rest => simp [separated]
    have hc : Fine (punctWord sep :: separated sep (y :: rest)) := Fine.cons (by simp [punctWord]) ⟨hr.1, hr.2, hyr⟩
    have := hx.append hc
    simp only [separated]
    exact ⟨this.1, this.2.1⟩

theorem fine_enclose {o c : String} {items : List (List Word)} (h : ∀ x ∈ items, Fine x) :
    Fine (enclose o c items) := by
  obtain ⟨h1, h2⟩ := fine_separated "," items h
  simp only [enclose]
  refine Fine.cons (by simp [punctWord]) ?_
  exact ⟨breaksOK_append _ _ h1 (by rfl) (fun h' => absurd h' h2), by simp [punctWord], by simp⟩

theorem nil_not_mem_separated (sep : String) :
    ∀ items : List (List Word), (∀ x ∈ items, [] ∉ x) → [] ∉ separated sep items
  | [], _ => by simp [separated]
  | [x], h => by simpa [separated] using h x (by simp)
  | x :: y :: rest, h => by
    simp only [separated, List.mem_append, List.mem_cons, not_or]
    refine ⟨h x (by simp), by simp [punctWord], ?_⟩
    simpa [separated] using nil_not_mem_separated sep (y :: rest) (fun z hz => h z (by simp_all))

theorem symbol_ne (s : String) (h : s ≠ "") : symbol s ≠ [] := by
  unfold symbol; split
  · rename_i h'; intro he; simp at he; exact h he
  · split <;> simp [keywordWord, punctWord]

mutual

/-- A type's words have tokens: no `lineBreak` is among them. -/
theorem TypeExpr.fine : ∀ t : TypeExpr, [] ∉ t.words
  | .keyword _ name => by simp only [TypeExpr.words]; split <;> simp [keywordWord, identWord]
  | .null _ => by simp [TypeExpr.words, keywordWord]
  | .literal _ (.string _) | .literal _ (.number _) | .literal _ (.bigint _) | .literal _ (.bool _) => by
    simp [TypeExpr.words, LitType.words, keywordWord]
  | .ref _ name [] => by simp [TypeExpr.words, identWord]
  | .ref _ name (a :: args) => by
    have := nil_not_mem_separated "," _ (TypeExpr.fineAll (a :: args))
    simp only [TypeExpr.words, List.mem_cons, List.mem_append, not_or]
    simp [identWord, punctWord, this]
  | .array _ elem => by
    have := TypeExpr.fine elem
    simp only [TypeExpr.words, List.mem_append, List.mem_cons, not_or]
    simp [punctWord, this]
  | .union _ [] => by simp [TypeExpr.words, TypeExpr.wordsOf, separated]
  | .union _ [m] => by
    have := TypeExpr.fine m
    simp only [TypeExpr.words, List.mem_cons, not_or]
    simp [punctWord, this]
  | .union _ (a :: b :: ms) => by
    simp only [TypeExpr.words]
    exact nil_not_mem_separated "|" _ (TypeExpr.fineAll (a :: b :: ms))
  | .paren _ inner => by
    have := TypeExpr.fine inner
    simp only [TypeExpr.words, List.mem_cons, List.mem_append, not_or]
    simp [punctWord, this]

theorem TypeExpr.fineAll : ∀ ts : List TypeExpr, ∀ x ∈ TypeExpr.wordsOf ts, [] ∉ x
  | [], _, hx => by simp [TypeExpr.wordsOf] at hx
  | t :: ts, x, hx => by
    simp only [TypeExpr.wordsOf, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact TypeExpr.fine t
    · exact TypeExpr.fineAll ts x hx

end

/-- The words before the `(` of a call, and its arguments. -/
theorem Fine.call {c : Expr} {items : List (List Word)} (h : ∀ x ∈ items, Fine x) :
    Fine (callBreak c ++ enclose "(" ")" items) := by
  have he := fine_enclose (o := "(") (c := ")") h
  unfold callBreak; split
  · refine ⟨?_, by simpa [getLast?_append_ne he.2.2] using he.2.1, by simp⟩
    simp only [List.singleton_append, lineBreak, breaksOK, Bool.and_eq_true, beq_iff_eq]
    exact ⟨by simp [enclose, punctWord], he.1⟩
  · simpa using he

theorem propertyName_ne (n : String) : propertyName n ≠ [] := by
  unfold propertyName; split <;> simp [keywordWord, identWord]

mutual

theorem Expr.fine : ∀ e : Expr, Fine e.words
  | .ident _ n => by simpa [Expr.words] using Fine.word (w := identWord n) (by simp [identWord])
  | .number _ t => by simpa [Expr.words] using Fine.word (w := [.number t]) (by simp)
  | .bigint _ t => by simpa [Expr.words] using Fine.word (w := [.bigint t]) (by simp)
  | .string _ v => by simpa [Expr.words] using Fine.word (w := [.string v]) (by simp)
  | .bool _ b => by simpa [Expr.words] using Fine.word (w := keywordWord (if b then "true" else "false")) (by simp [keywordWord])
  | .null _ => by simpa [Expr.words] using Fine.word (w := keywordWord "null") (by simp [keywordWord])
  | .array _ es => by simpa [Expr.words] using fine_enclose (o := "[") (c := "]") (Expr.fineAll es)
  | .object _ ps => by simpa [Expr.words] using fine_enclose (o := "{") (c := "}") (Property.fineAll ps)
  | .paren _ i => by
    simpa [Expr.words] using Fine.cons (w := punctWord "(") (by simp [punctWord])
      ((Expr.fine i).append (Fine.word (w := punctWord ")") (by simp [punctWord])))
  | .member _ o n => by
    simpa [Expr.words] using (Expr.fine o).append
      (Fine.cons (w := punctWord ".") (by simp [punctWord]) (Fine.word (propertyName_ne n)))
  | .index _ o i => by
    simpa [Expr.words] using (Expr.fine o).append (Fine.cons (w := punctWord "[") (by simp [punctWord])
      ((Expr.fine i).append (Fine.word (w := punctWord "]") (by simp [punctWord]))))
  | .call _ c as => by
    simpa [Expr.words, List.append_assoc] using (Expr.fine c).append (Fine.call (c := c) (Expr.fineAll as))
  | .unary _ op a => by
    simpa [Expr.words] using Fine.cons (symbol_ne _ (by cases op <;> simp [UnaryOp.symbol])) (Expr.fine a)
  | .prefix _ op a => by
    simpa [Expr.words] using Fine.cons (w := punctWord op.symbol) (by simp [punctWord]) (Expr.fine a)
  | .postfix _ op a => by
    simpa [Expr.words] using (Expr.fine a).append (Fine.word (w := punctWord op.symbol) (by simp [punctWord]))
  | .binary _ op l r => by
    simpa [Expr.words] using (Expr.fine l).append
      (Fine.cons (symbol_ne _ (by cases op <;> simp [BinOp.symbol])) (Expr.fine r))
  | .cond _ t a b => by
    simpa [Expr.words, List.append_assoc] using (Expr.fine t).append
      (Fine.cons (w := punctWord "?") (by simp [punctWord]) ((Expr.fine a).append
        (Fine.cons (w := punctWord ":") (by simp [punctWord]) (Expr.fine b))))
  | .assign _ op t v => by
    simpa [Expr.words] using (Expr.fine t).append
      (Fine.cons (symbol_ne _ (by cases op <;> simp [AssignOp.symbol])) (Expr.fine v))

theorem Expr.fineAll : ∀ es : List Expr, ∀ x ∈ Expr.wordsOf es, Fine x
  | [], _, hx => by simp [Expr.wordsOf] at hx
  | e :: es, x, hx => by
    simp only [Expr.wordsOf, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Expr.fine e
    · exact Expr.fineAll es x hx

theorem Property.fine : ∀ q : Property, Fine q.words
  | .shorthand _ n => by simpa [Property.words] using Fine.word (w := identWord n) (by simp [identWord])
  | .keyValue _ k v => by
    have hk : Fine k.words := by
      cases k with
      | ident n => simpa [PropKey.words] using Fine.word (propertyName_ne n)
      | string v => simpa [PropKey.words] using Fine.word (w := [.string v]) (by simp)
      | number t => simpa [PropKey.words] using Fine.word (w := [.number t]) (by simp)
    simpa [Property.words] using hk.append (Fine.cons (w := punctWord ":") (by simp [punctWord]) (Expr.fine v))

theorem Property.fineAll : ∀ ps : List Property, ∀ x ∈ Property.wordsOf ps, Fine x
  | [], _, hx => by simp [Property.wordsOf] at hx
  | q :: ps, x, hx => by
    simp only [Property.wordsOf, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Property.fine q
    · exact Property.fineAll ps x hx

end

/-! ### Lines -/

/-- The words of a line: `breaksOK` accepts them, and the last word has tokens. -/
def LineOK (ws : List Word) : Prop := breaksOK ws = true ∧ ws.getLast? ≠ some []

theorem LineOK.append {a b : List Word} (ha : LineOK a) (hb : LineOK b) : LineOK (a ++ b) := by
  refine ⟨breaksOK_append a b ha.1 hb.1 (fun h => absurd h ha.2), ?_⟩
  rw [List.getLast?_append]
  cases h : b.getLast? with
  | none => simpa using ha.2
  | some x => simpa [h] using hb.2

theorem LineOK.nil : LineOK [] := ⟨rfl, by simp⟩

theorem Fine.line {ws : List Word} (h : Fine ws) : LineOK ws := ⟨h.1, h.2.1⟩

theorem LineOK.word {w : Word} (hw : w ≠ []) : LineOK [w] := (Fine.word hw).line

theorem LineOK.cons {w : Word} {ws : List Word} (hw : w ≠ []) (h : LineOK ws) : LineOK (w :: ws) := by
  simpa using (LineOK.word hw).append h

theorem TypeExpr.line (t : TypeExpr) : LineOK t.words :=
  ⟨breaksOK_of_ne _ (fun _ hw he => TypeExpr.fine t (he ▸ hw)),
    fun hl => TypeExpr.fine t (List.mem_of_getLast? hl)⟩

theorem VarKind.word_ne (k : VarKind) : k.word ≠ [] := by cases k <;> simp [VarKind.word, keywordWord, identWord]

theorem typeAnnotation_line : ∀ a : Option TypeExpr, LineOK (typeAnnotation a)
  | some t => LineOK.cons (by simp [punctWord]) (TypeExpr.line t)
  | none => LineOK.nil

theorem VarDecl.line (d : VarDecl) : LineOK d.words := by
  simp only [VarDecl.words]
  refine (((LineOK.cons d.kind.word_ne (LineOK.word (w := identWord d.name) (by simp [identWord]))).append
    (typeAnnotation_line _)).append ?_).append (LineOK.word (w := punctWord ";") (by simp [punctWord]))
  split
  · exact LineOK.cons (by simp [punctWord]) (Expr.fine _).line
  · exact LineOK.nil

mutual

theorem Stmt.lineOK : ∀ (st : Stmt) (d : Nat), ∀ l ∈ st.lines d, LineOK l.2
  | .varDecl _ v, d, l, hl => by simp [Stmt.lines] at hl; subst hl; exact v.line
  | .exprStmt _ e, d, l, hl => by
    simp [Stmt.lines] at hl; subst hl
    exact (Expr.fine e).line.append (LineOK.word (w := punctWord ";") (by simp [punctWord]))
  | .returnStmt _ none, d, l, hl => by
    simp [Stmt.lines] at hl; subst hl
    exact LineOK.cons (by simp [keywordWord]) (LineOK.word (w := punctWord ";") (by simp [punctWord]))
  | .returnStmt _ (some e), d, l, hl => by
    simp [Stmt.lines] at hl; subst hl
    exact LineOK.cons (by simp [keywordWord])
      ((Expr.fine e).line.append (LineOK.word (w := punctWord ";") (by simp [punctWord])))
  | .ifStmt _ test t none, d, l, hl => by
    simp only [Stmt.lines, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact LineOK.cons (by simp [keywordWord]) (LineOK.cons (by simp [punctWord])
        ((Expr.fine test).line.append (LineOK.word (w := punctWord ")") (by simp [punctWord]))))
    · exact Stmt.lineOK t _ l hl
  | .ifStmt _ test t (some e), d, l, hl => by
    simp only [Stmt.lines, List.mem_cons, List.mem_append] at hl
    rcases hl with (rfl | hl) | (rfl | hl)
    · exact LineOK.cons (by simp [keywordWord]) (LineOK.cons (by simp [punctWord])
        ((Expr.fine test).line.append (LineOK.word (w := punctWord ")") (by simp [punctWord]))))
    · exact Stmt.lineOK t _ l hl
    · exact LineOK.word (by simp [keywordWord])
    · exact Stmt.lineOK e _ l hl
  | .forOfStmt _ kind name it body, d, l, hl => by
    simp only [Stmt.lines, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact LineOK.cons (by simp [keywordWord]) (LineOK.cons (by simp [punctWord]) (LineOK.cons kind.word_ne
        (LineOK.cons (by simp [identWord]) (LineOK.cons (by simp [identWord])
          ((Expr.fine it).line.append (LineOK.word (w := punctWord ")") (by simp [punctWord])))))))
    · exact Stmt.lineOK body _ l hl
  | .whileStmt _ test body, d, l, hl => by
    simp only [Stmt.lines, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact LineOK.cons (by simp [keywordWord]) (LineOK.cons (by simp [punctWord])
        ((Expr.fine test).line.append (LineOK.word (w := punctWord ")") (by simp [punctWord]))))
    · exact Stmt.lineOK body _ l hl
  | .block _ body, d, l, hl => by
    simp only [Stmt.lines, List.mem_cons, List.mem_append, List.mem_singleton] at hl
    rcases hl with (rfl | hl) | (rfl | hl)
    · exact LineOK.word (by simp [punctWord])
    · exact Stmt.lineOKAll body _ l hl
    · exact LineOK.word (by simp [punctWord])
    · simp at hl
  | .breakStmt _, d, l, hl | .continueStmt _, d, l, hl => by
    simp [Stmt.lines] at hl; subst hl
    exact LineOK.cons (by simp [keywordWord]) (LineOK.word (w := punctWord ";") (by simp [punctWord]))
  | .empty _, d, l, hl => by simp [Stmt.lines] at hl; subst hl; exact LineOK.word (by simp [punctWord])

theorem Stmt.lineOKAll : ∀ (ss : List Stmt) (d : Nat), ∀ l ∈ Stmt.linesOf d ss, LineOK l.2
  | [], _, l, hl => by simp [Stmt.linesOf] at hl
  | s :: ss, d, l, hl => by
    simp only [Stmt.linesOf, List.mem_append] at hl
    rcases hl with hl | hl
    · exact Stmt.lineOK s d l hl
    · exact Stmt.lineOKAll ss d l hl

end

theorem Fine.ofLine {w : Word} {ws : List Word} (hw : w ≠ []) (h : LineOK ws) : Fine (w :: ws) :=
  ⟨(LineOK.cons hw h).1, (LineOK.cons hw h).2, by simp⟩

theorem exportWords_line (e : Bool) : LineOK (exportWords e) := by
  cases e
  · exact LineOK.nil
  · exact LineOK.word (by simp [keywordWord])

theorem Decl.lineOK : ∀ d : Decl, ∀ l ∈ d.lines, LineOK l.2
  | .import _ names source, l, hl => by
    simp [Decl.lines] at hl; subst hl
    have hn : ∀ x ∈ names.map ImportName.words, Fine x := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨n, _, rfl⟩ := hx
      unfold ImportName.words; split
      · exact Fine.ofLine (by simp [identWord]) (LineOK.word (by simp [identWord]))
      · exact Fine.word (by simp [identWord])
    exact LineOK.cons (by simp [keywordWord]) ((fine_enclose hn).line.append
      (LineOK.cons (by simp [identWord]) (LineOK.cons (by simp) (LineOK.word (by simp [punctWord])))))
  | .function _ exported name params rt body, l, hl => by
    simp only [Decl.lines, List.mem_cons] at hl
    rcases hl with rfl | hl
    · have hp : ∀ x ∈ params.map Param.words, Fine x := by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨p, _, rfl⟩ := hx
        exact Fine.ofLine (by simp [identWord]) (typeAnnotation_line _)
      have := (exportWords_line exported).append (LineOK.cons (w := keywordWord "function") (by simp [keywordWord])
        (LineOK.cons (w := identWord name) (by simp [identWord])
          ((fine_enclose (o := "(") (c := ")") hp).line.append (typeAnnotation_line rt))))
      simpa [List.append_assoc] using this
    · exact Stmt.lineOK body 0 l hl
  | .interface _ exported name fields, l, hl => by
    simp only [Decl.lines, List.mem_cons, List.mem_append, List.mem_map, List.mem_singleton] at hl
    rcases hl with (rfl | ⟨f, _, rfl⟩) | (rfl | hl)
    · exact (exportWords_line exported).append (LineOK.cons (by simp [identWord]) (LineOK.cons (by simp [identWord])
        (LineOK.word (by simp [punctWord]))))
    · have h1 : LineOK (if f.readonly then [identWord "readonly"] else []) := by
        split
        · exact LineOK.word (by simp [identWord])
        · exact LineOK.nil
      have h2 : LineOK (if f.optional then [punctWord "?"] else []) := by
        split
        · exact LineOK.word (by simp [punctWord])
        · exact LineOK.nil
      have := ((h1.append (LineOK.word (propertyName_ne f.name))).append h2).append
        (LineOK.cons (w := punctWord ":") (by simp [punctWord])
          ((TypeExpr.line f.type).append (LineOK.word (w := punctWord ";") (by simp [punctWord]))))
      simpa [Field.words, List.append_assoc] using this
    · exact LineOK.word (by simp [punctWord])
    · simp at hl
  | .typeAlias _ exported name ty, l, hl => by
    simp [Decl.lines] at hl; subst hl
    exact (exportWords_line exported).append (LineOK.cons (by simp [identWord]) (LineOK.cons (by simp [identWord])
      (LineOK.cons (by simp [punctWord]) ((TypeExpr.line ty).append (LineOK.word (by simp [punctWord]))))))
  | .exportedVar _ v, l, hl => by
    simp [Decl.lines] at hl; subst hl
    exact LineOK.cons (by simp [keywordWord]) v.line
  | .stmt st, l, hl => Stmt.lineOK st 0 l hl

/-- Every line that the printer writes for a module meets `breaksOK`. -/
theorem Module.breaksOK (m : Module) : ∀ l ∈ m.lines, breaksOK l.2 = true := by
  intro l hl
  simp only [Module.lines, List.mem_flatMap] at hl
  obtain ⟨d, _, hd⟩ := hl
  exact (Decl.lineOK d l hd).1


/-! ### The round trip on source text -/

/-- The round trip on source text for a module: the parser reads the printed
source of every well-formed module whose printed words lex back as that
module, apart from spans. -/
theorem source_reads {T : Edition} (m : Module) (hm : m.wf T = true) (hw : ∀ l ∈ m.lines, WordsOK T l.2) :
    ∃ m', parseChars m.source.toList T = .ok m' ∧ m'.erase = m.erase := by
  obtain ⟨ts, e, hlex, hlaid, he⟩ := lexChars_render T m.lines (fun l hl w hw' => hw l hl w hw') (Module.breaksOK m)
  obtain ⟨m', s', hp, herase⟩ := module_reads m hm
    { rest := ts ++ [e], left := (ts ++ [e]).length,
      eof := (ts ++ [e]).getLastD { kind := .eof, span := ⟨⟨1, 1⟩, ⟨1, 1⟩⟩, newlineBefore := false },
      target := T } ts e rfl rfl rfl he rfl hlaid
  refine ⟨m', ?_, herase⟩
  simp only [List.getLastD_concat, List.length_append, List.length_singleton] at hp
  simp [parseChars, Module.source, hlex, parseTokens, EStateM.run, bind, Except.bind, hp]

/-- The parser's round trip on source text: when the parser gives the module
`m` from some characters, it reads the printed source of `m` as `m` again,
apart from spans. -/
theorem parseChars_reads {T : Edition} {chars : List Char} {m : Module} (h : parseChars chars T = .ok m) :
    ∃ m', parseChars m.source.toList T = .ok m' ∧ m'.erase = m.erase := by
  simp only [parseChars] at h
  cases hl : lexChars chars T with
  | error e => rw [hl] at h; cases h
  | ok toks =>
    rw [hl] at h
    obtain ⟨hwf, hw⟩ := parseTokens_wf (lexChars_last_eof T chars toks hl)
      (fun t ht => (lexChars_ok_kinds T chars toks hl t ht).imp_right (by simpa [Word.ok] using ·)) h
    exact source_reads m hwf hw

end tolean.TypeScript.Syntax
