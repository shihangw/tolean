import tolean.TypeScript.Syntax.RoundTripDecl
import tolean.TypeScript.Syntax.RoundTripLex

/-!
Every tree that the parser gives is well formed: it satisfies the `wf`
predicates under which `module_reads` proves the round trip.

The proofs run each function of the parser backwards. From `p s = .ok x s'`,
`Parse.bind_ok` splits a do-block into its steps, and each step gives what
the parser checked there. The parser reads only tokens that the lexer gives,
and the last token is the end of the file (`Ready`). So every token that the
parser reads is one that it moves past.

Most of `wf` is the shape of a tree, which follows from the function that
read it. `afterOK` is different: it looks at the printed tokens after a
node, and the parser looked at the source tokens after it. The two agree
where it matters. The parser reads the same brackets, `;` and `>` that the
printer writes (`skel`), and the printed tokens after a node end the scan for
a `>` wherever the source tokens end it (`Follows`).

The lexer reads the printed source back only when each printed word is one
that it gives (`Word.ok`). A name or a number that the parser read comes from
a token, and every token that the lexer gives has such a kind (`Ready`). So
each result of the parser also carries `WordsOK` for its printed words:
`GaveE` for expressions, `StmtOK` for statements and `DeclOK` for
declarations.
-/

namespace tolean.TypeScript.Syntax

open tolean

/-! ### Token skeletons -/

/-- The token kinds that `closesKinds` reads: brackets, `;`, `>` and the end
of the file. -/
def skelKind : TokenKind → Bool
  | .punct "(" | .punct "[" | .punct "{" | .punct ")" | .punct "]" | .punct "}" | .punct ";" | .punct ">"
  | .eof => true
  | _ => false

/-- The kinds of `ks` that `closesKinds` reads. -/
def skel (ks : List TokenKind) : List TokenKind := ks.filter skelKind

theorem closesKinds_skel : ∀ (d : Nat) (ks : List TokenKind), closesKinds d (skel ks) = closesKinds d ks
  | _, [] => rfl
  | d, k :: ks => by
    have ih := fun d' => closesKinds_skel d' ks
    cases k with
    | punct p =>
      by_cases h : skelKind (.punct p) = true
      · simp only [skel, List.filter_cons, h, ↓reduceIte] at ih ⊢
        simp only [closesKinds]
        split <;> simp_all [skelKind]
      · simp only [skel, List.filter_cons, h, Bool.false_eq_true, ↓reduceIte] at ih ⊢
        rw [ih d]
        simp only [closesKinds]
        split <;> simp_all [skelKind]
    | eof => simp [skel, skelKind, closesKinds]
    | _ => simp only [skel, List.filter_cons, skelKind, Bool.false_eq_true, ↓reduceIte, closesKinds] at ih ⊢; exact ih d

theorem skel_append (a b : List TokenKind) : skel (a ++ b) = skel a ++ skel b := by
  simp [skel, List.filter_append]

/-- `closesKinds` gives the same answer on two lists with the same skeleton. -/
theorem closesKinds_of_skel {d : Nat} {a b : List TokenKind} (h : skel a = skel b) :
    closesKinds d a = closesKinds d b := by
  rw [← closesKinds_skel d a, h, closesKinds_skel]

/-! ### What follows a node -/

/-- `after`, the printed tokens after a node, ends the scan for a `>` wherever
`rest`, the tokens after the node in the source, ends it. And `after` does
not start with `{`. -/
def Follows (rest after : List TokenKind) : Prop :=
  (∀ a, closesKinds 0 (a ++ rest) = false → closesKinds 0 (a ++ after) = false) ∧
    after.head? ≠ some (.punct "{")

/-- The scan of `a ++ [c]`, where `c` is `;` or `)`, finds a `>` only in `a`. -/
theorem closesKinds_end : ∀ (d : Nat) (a rest : List TokenKind) (c : String), (c = ";" ∨ c = ")") →
    closesKinds d (a ++ rest) = false → closesKinds d (a ++ [.punct c]) = false
  | d, [], rest, c, hc, _ => by
    rcases hc with rfl | rfl <;> cases d <;> simp [closesKinds]
  | d, k :: a, rest, c, hc, h => by
    have ih := fun d' => closesKinds_end d' a rest c hc
    simp only [List.cons_append, closesKinds] at h ⊢
    split at h <;> simp_all

theorem follows_end {rest : List TokenKind} {c : String} (hc : c = ";" ∨ c = ")") :
    Follows rest [.punct c] :=
  ⟨fun a h => closesKinds_end 0 a rest c hc h, by rcases hc with rfl | rfl <;> simp⟩

/-- The scan of `a ++ [:]` finds a `>` only in `a`. -/
theorem closesKinds_colon : ∀ (d : Nat) (a rest : List TokenKind),
    closesKinds d (a ++ rest) = false → closesKinds d (a ++ [.punct ":"]) = false
  | d, [], _, _ => by simp [closesKinds]
  | d, k :: a, rest, h => by
    have ih := fun d' => closesKinds_colon d' a rest
    simp only [List.cons_append, closesKinds] at h ⊢
    split at h <;> simp_all

/-- A `:` follows an expression as the end of a statement does. -/
theorem follows_colon {rest : List TokenKind} : Follows rest [.punct ":"] :=
  ⟨fun a h => closesKinds_colon 0 a rest h, by simp⟩

/-- Tokens with the same skeleton before both lists keep `Follows`. -/
theorem Follows.prefix {rest after p p' : List TokenKind} (h : Follows rest after) (hs : skel p = skel p')
    (hh : p'.head? ≠ some (.punct "{")) : Follows (p ++ rest) (p' ++ after) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · have h1 : closesKinds 0 ((a ++ p') ++ rest) = false := by
      rw [← ha]; apply closesKinds_of_skel; simp [skel_append, hs]
    simpa using h.1 (a ++ p') h1
  · cases p' with
    | nil => simpa using h.2
    | cons k _ => simpa using hh

/-! ### States -/

/-- The state holds its tokens and their count, the last token is `eof`, the
end of the file, and every other token is one that the lexer reads back for
the state's target (`TokenKind.ok`), as every token that the lexer gives is.
So no token stands for `>=` or `>>`, which the lexer gives as `>` tokens. -/
def Ready (s : ParseState) : Prop :=
  Parse.Good s ∧ s.rest.getLast? = some s.eof ∧ s.eof.kind = .eof ∧
    ∀ t ∈ s.rest, t.kind = .eof ∨ TokenKind.ok s.target t.kind = true

/-- Every word of `ws` lexes back, for the target `T`. -/
def WordsOK (T : Edition) (ws : List Word) : Prop := ∀ w ∈ ws, Word.ok T w = true

theorem WordsOK.nil {T : Edition} : WordsOK T [] := by simp [WordsOK]

theorem WordsOK.append {T : Edition} {a b : List Word} (ha : WordsOK T a) (hb : WordsOK T b) :
    WordsOK T (a ++ b) := by
  intro w hw; rcases List.mem_append.mp hw with h | h
  · exact ha w h
  · exact hb w h

theorem WordsOK.cons {T : Edition} {w : Word} {ws : List Word} (hw : Word.ok T w = true) (h : WordsOK T ws) :
    WordsOK T (w :: ws) := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx
  · exact hw
  · exact h x hx

theorem WordsOK.word {T : Edition} {w : Word} (hw : Word.ok T w = true) : WordsOK T [w] :=
  WordsOK.cons hw WordsOK.nil

theorem ok_punct {T : Edition} {p : String} (h : Lex.punctuators.contains p = true) :
    Word.ok T [.punct p] = true := by simpa [Word.ok, TokenKind.ok] using h

theorem ok_keyword {T : Edition} {w : String} (h : Lex.reservedWords.contains w = true) :
    Word.ok T [.keyword w] = true := by simpa [Word.ok, TokenKind.ok] using h

theorem binOp_ok (T : Edition) (op : BinOp) : Word.ok T (symbol op.symbol) = true := by
  cases op <;> simp (config := { decide := true }) [symbol, BinOp.symbol, Lex.reservedWords, punctWord, keywordWord,
    Word.ok, TokenKind.ok, Lex.punctuators]

theorem assignOp_ok (T : Edition) (op : AssignOp) : Word.ok T (symbol op.symbol) = true := by
  cases op <;> simp (config := { decide := true }) [symbol, AssignOp.symbol, punctWord,
    Word.ok, TokenKind.ok, Lex.punctuators]

/-- A token that is not the end of the file has a token after it. -/
theorem Ready.more {s : ParseState} {x : Token} {r : List Token} (h : Ready s) (hs : s.rest = x :: r)
    (hx : x.kind ≠ .eof) : r ≠ [] := by
  rintro rfl
  have := h.2.1
  simp [hs] at this
  exact hx (this ▸ h.2.2.1)

/-- A state whose tokens end the tokens of a ready state is ready. -/
theorem Ready.suffix {s s' : ParseState} {a : List Token} (h : Ready s) (hs : s.rest = a ++ s'.rest)
    (hr : s'.rest ≠ []) (hl : s'.left = s'.rest.length) (he : s'.eof = s.eof) (ht : s'.target = s.target) :
    Ready s' := by
  refine ⟨⟨hr, hl⟩, ?_, he ▸ h.2.2.1, fun t ht' => ht ▸ h.2.2.2 t (by rw [hs]; exact List.mem_append_right _ ht')⟩
  have h1 := h.2.1
  obtain ⟨u, r', hu⟩ := List.exists_cons_of_ne_nil hr
  rw [hs, hu] at h1
  rw [hu, he]
  simpa [List.getLast?_append] using h1

theorem Ready.past {s : ParseState} {x : Token} {r : List Token} (h : Ready s) (hs : s.rest = x :: r)
    (hr : r ≠ []) : Ready (past s x r) :=
  h.suffix (a := [x]) (by simpa using hs) hr (by have := h.1.2; simp [hs] at this; simp [this]) rfl rfl

/-- `advance` reads a token that is not the end of the file. -/
theorem advance_past {s : ParseState} {x : Token} {r : List Token} (h : Ready s) (hs : s.rest = x :: r)
    (hx : x.kind ≠ .eof) : Parse.advance s = .ok x (past s x r) :=
  Parse.advance_cons hs (h.more hs hx)

/-- Two runs from one state give one result. -/
theorem ok_unique {α : Type} {x : ParseM α} {s s₁ s₂ : ParseState} {a b : α} (h₁ : x s = .ok a s₁)
    (h₂ : x s = .ok b s₂) : a = b ∧ s₁ = s₂ := by
  rw [h₁] at h₂; cases h₂; exact ⟨rfl, rfl⟩

/-- `expectPunct p` reads a `p`. -/
theorem expectPunct_inv {s s' : ParseState} {p : String} {t : Token} (h : Ready s)
    (he : Parse.expectPunct p s = .ok t s') :
    t.kind = .punct p ∧ ∃ r, s.rest = t :: r ∧ s' = past s t r ∧ Ready s' := by
  obtain ⟨x, r, hs⟩ : ∃ x r, s.rest = x :: r := by
    cases hr : s.rest with
    | nil => exact absurd hr h.1.1
    | cons x r => exact ⟨x, r, rfl⟩
  simp only [Parse.expectPunct] at he
  rw [Parse.bind_eq (Parse.peek_eq hs)] at he
  by_cases hp : x.isPunct p = true
  · rw [if_pos hp] at he
    have hk : x.kind = .punct p := by simpa [Token.isPunct] using hp
    have hx : x.kind ≠ .eof := by rw [hk]; simp
    rw [advance_past h hs hx] at he
    obtain ⟨rfl, rfl⟩ : x = t ∧ past s x r = s' := by simpa using he
    exact ⟨hk, r, hs, rfl, h.past hs (h.more hs hx)⟩
  · rw [if_neg hp] at he
    exact absurd he (Parse.unexpected_ne_ok _ _ _ _ _)

/-- `readName` reads a name that the parser allows. -/
theorem readName_inv {s s' : ParseState} {n : String} (h : Ready s) (he : Parse.readName s = .ok n s') :
    ∃ t r, t.kind = .ident n ∧ n ∉ Parse.refusedNames ∧ s.rest = t :: r ∧ s' = past s t r ∧ Ready s' := by
  obtain ⟨x, r, hs⟩ : ∃ x r, s.rest = x :: r := by
    cases hr : s.rest with
    | nil => exact absurd hr h.1.1
    | cons x r => exact ⟨x, r, rfl⟩
  simp only [Parse.readName] at he
  generalize hk : x.kind = k at *
  cases k with
  | ident name =>
    have hx : x.kind ≠ .eof := by rw [hk]; simp
    rw [Parse.bind_eq (advance_past h hs hx)] at he
    simp only [hk] at he
    by_cases hn : name ∈ Parse.refusedNames
    · simp [hn, Functor.map, EStateM.map, Parse.failAt, throw, throwThe, MonadExceptOf.throw,
        EStateM.throw] at he
    · simp [hn, pure] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨x, r, hk, hn, hs, rfl, h.past hs (h.more hs hx)⟩
  | eof =>
    simp only [Parse.advance, hs, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind] at he
    split at he <;> simp_all [set, MonadStateOf.set, EStateM.set, pure, EStateM.pure, Parse.unexpected,
      Parse.failAt, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  | _ =>
    simp only [Parse.advance, hs, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind] at he
    split at he <;> simp_all [set, MonadStateOf.set, EStateM.set, pure, EStateM.pure, Parse.unexpected,
      Parse.failAt, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem outOfFuel_ne_ok {α : Type} (s s' : ParseState) (a : α) : (Parse.outOfFuel (A := α)) s ≠ .ok a s' := by
  simp only [Parse.outOfFuel]
  intro h
  rw [Parse.bind_ok] at h
  obtain ⟨_, _, _, h⟩ := h
  exact Parse.failAt_ne_ok _ _ _ _ _ h

/-- A property of a loop's value and state that each step keeps holds when the
loop ends, and so it does before the last step, which said to stop. -/
theorem iterate_inv {σ : Type} {step : σ → ParseM (σ × Bool)} {I : σ → ParseState → Prop}
    (hstep : ∀ a s a' b s', I a s → step a s = .ok (a', b) s' → I a' s') :
    ∀ (n : Nat) (a : σ) (s : ParseState) (r : σ) (s' : ParseState), I a s →
      Parse.iterate n a step s = .ok r s' → I r s' ∧ ∃ a₁ s₁, I a₁ s₁ ∧ step a₁ s₁ = .ok (r, false) s'
  | 0, a, s, r, s', _, h => by
    simp only [Parse.iterate] at h; exact absurd h (outOfFuel_ne_ok _ _ _)
  | n + 1, a, s, r, s', hI, h => by
    rw [Parse.iterate_succ, Parse.bind_ok] at h
    obtain ⟨⟨a', b⟩, s₁, h₁, h⟩ := h
    have hI' := hstep a s a' b s₁ hI h₁
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Parse.pure_ok] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hI', a, s, hI, h₁⟩
    | true => exact iterate_inv hstep n a' s₁ r s' hI' (by simpa using h)

/-- The state has a first token. -/
theorem Ready.cons {s : ParseState} (h : Ready s) : ∃ x r, s.rest = x :: r := by
  cases hr : s.rest with
  | nil => exact absurd hr h.1.1
  | cons x r => exact ⟨x, r, rfl⟩

/-- `advance` reads the first token, and moves past it unless it is the end of the file. -/
theorem advance_inv {s s' : ParseState} {x t : Token} {r : List Token} (h : Ready s) (hs : s.rest = x :: r)
    (ha : Parse.advance s = .ok t s') : t = x ∧ (x.kind ≠ .eof → s' = past s x r ∧ Ready s') := by
  by_cases hx : x.kind = .eof
  · simp only [Parse.advance, hs, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, set,
      MonadStateOf.set, EStateM.set, pure, EStateM.pure] at ha
    split at ha <;> simp_all
  · obtain ⟨rfl, rfl⟩ := ok_unique ha (advance_past h hs hx)
    exact ⟨rfl, fun _ => ⟨rfl, h.past hs (h.more hs hx)⟩⟩

/-! ### Types -/

theorem primaryWF_arrayWF : ∀ t : TypeExpr, t.primaryWF = true → t.arrayWF = true
  | .keyword .., h | .null _, h | .literal .., h | .ref .., h | .paren .., h => by
    revert h; simp [TypeExpr.primaryWF, TypeExpr.arrayWF]
  | .tuple _ ro _, h => by cases ro <;> revert h <;> simp [TypeExpr.primaryWF, TypeExpr.arrayWF]
  | .array .., h | .union .., h => by simp [TypeExpr.primaryWF] at h

/-- A primary type is not `readonly [A, B]`. -/
theorem primaryWF_notReadonly : ∀ t : TypeExpr, t.primaryWF = true → t.isReadonlyTuple = false
  | .tuple _ ro _, h => by cases ro <;> simp_all [TypeExpr.primaryWF, TypeExpr.isReadonlyTuple]
  | .keyword .., _ | .null _, _ | .literal .., _ | .ref .., _ | .paren .., _ | .array .., _ | .union .., _ => rfl

theorem arrayWF_wf : ∀ t : TypeExpr, t.arrayWF = true → t.wf = true
  | .array _ _, h | .keyword .., h | .null _, h | .literal .., h | .ref .., h | .paren .., h | .tuple .., h => by
    revert h; simp [TypeExpr.arrayWF, TypeExpr.wf]
  | .union .., h => by simp [TypeExpr.arrayWF] at h

/-- What `p` gives when it reads a type for the target `T`: a type that `ok`
accepts, and a state that is still ready. -/
def GivesT (T : Edition) (ok : TypeExpr → Bool) (p : ParseM TypeExpr) : Prop :=
  ∀ s t s', Ready s → s.target = T → p s = .ok t s' → ok t = true ∧ Ready s' ∧ Kept s s'

/-- A token that is not the end of the file lexes back, as a word of its own. -/
theorem Ready.tok {s : ParseState} {x : Token} (h : Ready s) (hx : x ∈ s.rest) (hne : x.kind ≠ .eof) :
    Word.ok s.target [x.kind] = true := by
  rcases h.2.2.2 x hx with h' | h'
  · exact absurd h' hne
  · simpa [Word.ok] using h'

/-- `ws.all (Word.ok T)`, as `WordsOK` states it. -/
theorem wordsOK_iff {T : Edition} {ws : List Word} : ws.all (Word.ok T) = true ↔ WordsOK T ws := by
  simp [WordsOK]

theorem WordsOK.separated {T : Edition} {sep : String} (hs : Lex.punctuators.contains sep = true) :
    ∀ items : List (List Word), (∀ x ∈ items, WordsOK T x) → WordsOK T (separated sep items)
  | [], _ => WordsOK.nil
  | [x], h => by simpa [separated] using h x (by simp)
  | x :: y :: rest, h => by
    simp only [Syntax.separated]
    exact (h x (by simp)).append (WordsOK.cons (ok_punct hs)
      (WordsOK.separated hs (y :: rest) (fun z hz => h z (by simp_all))))

theorem WordsOK.wordsOf {T : Edition} : ∀ ts : List TypeExpr, (∀ t ∈ ts, WordsOK T t.words) →
    ∀ x ∈ TypeExpr.wordsOf ts, WordsOK T x
  | [], _, x, hx => by simp [TypeExpr.wordsOf] at hx
  | t :: ts, h, x, hx => by
    simp only [TypeExpr.wordsOf, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h t (by simp)
    · exact WordsOK.wordsOf ts (fun u hu => h u (by simp [hu])) x hx

/-- `skip 2` reads two tokens that another token follows. -/
theorem skip_two {s : ParseState} {x y : Token} {r : List Token} (hs : s.rest = x :: y :: r) (hr : r ≠ []) :
    Parse.skip 2 s = .ok () (past (past s x (y :: r)) y r) := by
  rw [Parse.skip, Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs (by simp))), Parse.skip,
    Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := past s x (y :: r)) rfl hr))]
  rfl

theorem arrayStep_inv {T : Edition} {start : Pos} {a a' : TypeExpr} {b : Bool} {s s' : ParseState}
    (hR : Ready s) (h : Parse.arrayStep start a s = .ok (a', b) s') :
    (a.arrayWF = true → a.isReadonlyTuple = false → a'.arrayWF = true ∧ a'.isReadonlyTuple = false) ∧
      (WordsOK T a.words → WordsOK T a'.words) ∧ Ready s' ∧ Kept s s' := by
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.arrayStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : (!x.isPunct "[" || x.newlineBefore) = true
  · rw [if_pos hc] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨fun ha hro => ⟨ha, hro⟩, id, hR, Kept.refl s⟩
  · rw [if_neg hc] at h
    have hx : x.kind = .punct "[" := by simp [Token.isPunct] at hc; exact hc.1
    have hr := hR.more hs (by rw [hx]; simp)
    obtain ⟨y, r', rfl⟩ := List.exists_cons_of_ne_nil hr
    rw [Parse.pure_bind, Parse.bind_eq (Parse.peekAt_eq (k := 1) (t := y) (by simp [hs]))] at h
    by_cases hy : y.isPunct "]" = true
    · have hyk : y.kind = .punct "]" := by simpa [Token.isPunct] using hy
      have hR₁ := hR.past hs hr
      have hR₂ := hR₁.past (s := past s x (y :: r')) rfl (hR₁.more rfl (by rw [hyk]; simp))
      simp only [hy, ↓reduceIte] at h
      rw [Parse.pure_bind, Parse.bind_eq (skip_two hs (hR₁.more rfl (by rw [hyk]; simp))),
        Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, _⟩, rfl⟩ := h
      exact ⟨fun ha hro => ⟨by simp only [TypeExpr.arrayWF, ha, hro, Bool.not_false, Bool.and_self], rfl⟩, fun ha => by
        simpa [TypeExpr.words] using ha.append (WordsOK.cons (ok_punct (by decide)) (WordsOK.word (ok_punct (by decide)))),
        hR₂, ⟨rfl, rfl, rfl, rfl⟩⟩
    · simp only [hy, Bool.false_eq_true, ↓reduceIte] at h
      rw [Parse.bind_ok] at h
      obtain ⟨_, _, hf, _⟩ := h
      exact absurd hf (Parse.failAt_ne_ok _ _ _ _ _)

/-- `m` joins items that are all `ok`. -/
theorem push_ok {ok : TypeExpr → Bool} {a : Array TypeExpr} {m : TypeExpr} (ha : ∀ x ∈ a.toList, ok x = true)
    (hm : ok m = true) : ∀ x ∈ (a.push m).toList, ok x = true := by
  intro x hx
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact ha x hx
  · exact hm

/-- The steps of the loop over the members of a union keep every member `ok`. -/
theorem unionStep_inv {T : Edition} {ok : TypeExpr → Bool} {p : ParseM TypeExpr} (hp : GivesT T ok p)
    {a a' : Array TypeExpr} {b : Bool} {s s' : ParseState} (hR : Ready s) (hT : s.target = T)
    (ha : ∀ m ∈ a.toList, ok m = true)
    (h : Parse.unionStep p a s = .ok (a', b) s') :
    (∀ m ∈ a'.toList, ok m = true) ∧ a.size ≤ a'.size ∧ Ready s' ∧ Kept s s' := by
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.unionStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hx : x.isPunct "|" = true
  · have hk : x.kind = .punct "|" := by simpa [Token.isPunct] using hx
    have hne : x.kind ≠ .eof := by rw [hk]; simp
    rw [if_neg (by simp [hx]), Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)),
      Parse.bind_ok] at h
    obtain ⟨m, s₁, hm, h⟩ := h
    obtain ⟨hmo, hR₁, hK₁⟩ := hp _ _ _ (hR.past hs (hR.more hs hne)) hT hm
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨push_ok ha hmo, by simp, hR₁, (Kept.past s x r).trans hK₁⟩
  · rw [if_pos (by simp [hx])] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨ha, Nat.le_refl _, hR, Kept.refl s⟩

/-- The steps of the loop over type arguments keep every argument `ok`. -/
theorem typeArgStep_inv {T : Edition} {ok : TypeExpr → Bool} {p : ParseM TypeExpr} (hp : GivesT T ok p)
    {a a' : Array TypeExpr} {b : Bool} {s s' : ParseState} (hR : Ready s) (hT : s.target = T)
    (ha : ∀ m ∈ a.toList, ok m = true)
    (h : Parse.typeArgStep p a s = .ok (a', b) s') : (∀ m ∈ a'.toList, ok m = true) ∧ Ready s' ∧ Kept s s' := by
  simp only [Parse.typeArgStep] at h
  rw [Parse.bind_ok] at h
  obtain ⟨m, s₁, hm, h⟩ := h
  obtain ⟨hmo, hR₁, hK₁⟩ := hp _ _ _ hR hT hm
  obtain ⟨x, r, hs⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hx : x.isPunct "," = true
  · have hk : x.kind = .punct "," := by simpa [Token.isPunct] using hx
    have hne : x.kind ≠ .eof := by rw [hk]; simp
    rw [if_neg (by simp [hx]), Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hs hne))] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨push_ok ha hmo, hR₁.past hs (hR₁.more hs hne), hK₁.trans (Kept.past _ x r)⟩
  · rw [if_pos (by simp [hx])] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨push_ok ha hmo, hR₁, hK₁⟩

/-- A step of the loop over type arguments, or over the elements of a tuple,
adds one. -/
theorem typeArgStep_push {p : ParseM TypeExpr} {a a' : Array TypeExpr} {b : Bool} {s s' : ParseState}
    (h : Parse.typeArgStep p a s = .ok (a', b) s') : ∃ m, a' = a.push m := by
  simp only [Parse.typeArgStep] at h
  rw [Parse.bind_ok] at h
  obtain ⟨m, s₁, -, h⟩ := h
  rw [Parse.bind_eq (show Parse.peek s₁ = .ok (s₁.rest[0]?.getD s₁.eof) s₁ from Parse.peekAt_rest s₁ 0)] at h
  by_cases hx : (s₁.rest[0]?.getD s₁.eof).isPunct "," = true
  · rw [if_neg (by simp [hx]), Parse.pure_bind, Parse.bind_ok] at h
    obtain ⟨_, _, _, h⟩ := h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    exact ⟨m, h.1.1.symm⟩
  · rw [if_pos (by simp [hx])] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    exact ⟨m, h.1.1.symm⟩

@[simp] theorem failAt_bind_ne_ok {α β : Type} (t : Token) (m : String) (f : α → ParseM β) (s s' : ParseState)
    (b : β) : (Parse.failAt (A := α) t m >>= f) s ≠ .ok b s' := by
  simp [Parse.failAt, throw, throwThe, MonadExceptOf.throw, EStateM.throw, bind, EStateM.bind]

@[simp] theorem unexpected_bind_ne_ok {α β : Type} (t : Token) (m : String) (f : α → ParseM β) (s s' : ParseState)
    (b : β) : (Parse.unexpected (A := α) t m >>= f) s ≠ .ok b s' := by
  simp [Parse.unexpected, Parse.failAt, throw, throwThe, MonadExceptOf.throw, EStateM.throw, bind, EStateM.bind]

/-- `wf` and `WordsOK`, as one test. -/
theorem both {T : Edition} {b : Bool} {ws : List Word} (h1 : b = true) (h2 : WordsOK T ws) :
    (b && ws.all (Word.ok T)) = true := by
  simp [h1, wordsOK_iff.mpr h2]

theorem both_left {T : Edition} {b : Bool} {ws : List Word} (h : (b && ws.all (Word.ok T)) = true) : b = true :=
  ((Bool.and_eq_true _ _).mp h).1

theorem both_right {T : Edition} {b : Bool} {ws : List Word} (h : (b && ws.all (Word.ok T)) = true) :
    WordsOK T ws :=
  wordsOK_iff.mp ((Bool.and_eq_true _ _).mp h).2

theorem types_give (T : Edition) : ∀ f : Nat,
    GivesT T (fun t => t.wf && t.words.all (Word.ok T)) (Parse.parseType f) ∧
      GivesT T (fun t => t.arrayWF && t.words.all (Word.ok T)) (Parse.parseArrayType f) ∧
      GivesT T (fun t => t.primaryWF && t.words.all (Word.ok T)) (Parse.parsePrimaryType f)
  | 0 => ⟨fun _ _ _ _ _ h => absurd h (by simp only [Parse.parseType]; exact outOfFuel_ne_ok _ _ _),
      fun _ _ _ _ _ h => absurd h (by simp only [Parse.parseArrayType]; exact outOfFuel_ne_ok _ _ _),
      fun _ _ _ _ _ h => absurd h (by simp only [Parse.parsePrimaryType]; exact outOfFuel_ne_ok _ _ _)⟩
  | f + 1 => by
    obtain ⟨ihT, ihA, ihP⟩ := types_give T f
    refine ⟨?_, ?_, ?_⟩
    · intro s t s' hR hT h
      obtain ⟨x, r, hs⟩ := hR.cons
      simp only [Parse.parseType] at h
      rw [Parse.bind_eq (Parse.peek_eq hs)] at h
      -- The members after the first, and the token after them.
      have hloop : ∀ (first : TypeExpr) (s₁ : ParseState) (n : Nat) (members : Array TypeExpr) (s₂ : ParseState),
          (first.arrayWF && first.words.all (Word.ok T)) = true → Ready s₁ → s₁.target = T →
          Parse.iterate n #[first] (Parse.unionStep (Parse.parseArrayType f)) s₁ = .ok members s₂ →
          (∀ m ∈ members.toList, (m.arrayWF && m.words.all (Word.ok T)) = true) ∧ 1 ≤ members.size ∧
            Ready s₂ ∧ Kept s₁ s₂ :=
        fun first s₁ n members s₂ hfw hR₁ hT₁ hm => (iterate_inv
          (I := fun a st => (∀ m ∈ a.toList, (m.arrayWF && m.words.all (Word.ok T)) = true) ∧ 1 ≤ a.size ∧
            Ready st ∧ Kept s₁ st)
          (fun a st a' b st' hI hst => by
            obtain ⟨h1, h2, h3, h4⟩ := unionStep_inv ihA hI.2.2.1 (hI.2.2.2.target_eq.trans hT₁) hI.1 hst
            exact ⟨h1, by omega, h3, hI.2.2.2.trans h4⟩) _ _ _ _ _
          ⟨by simpa using hfw, by simp, hR₁, Kept.refl _⟩ hm).1
      have hunion : ∀ (sp : Span) (ms : List TypeExpr), 1 ≤ ms.length →
          (∀ m ∈ ms, (m.arrayWF && m.words.all (Word.ok T)) = true) →
          ((TypeExpr.union sp ms).wf && (TypeExpr.union sp ms).words.all (Word.ok T)) = true := by
        intro sp ms hlen hall
        have hw : ∀ m ∈ ms, WordsOK T m.words := fun m hm => both_right (hall m hm)
        have ha : ∀ m ∈ ms, m.arrayWF = true := fun m hm => both_left (hall m hm)
        match ms, hlen with
        | [m], _ =>
          refine both (by simpa [TypeExpr.wf] using ha) ?_
          simpa [TypeExpr.words] using WordsOK.cons (ok_punct (by decide)) (hw m (by simp))
        | m₁ :: m₂ :: ms', _ =>
          refine both ?_ ?_
          · simp only [TypeExpr.wf, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨by simp, (allArrayWF_iff _).mpr ha⟩
          · simp only [TypeExpr.words]
            exact WordsOK.separated (sep := "|") (by decide) _ (WordsOK.wordsOf _ hw)
      by_cases hl : x.isPunct "|" = true
      · have hne : x.kind ≠ .eof := by simp [Token.isPunct] at hl; rw [hl]; simp
        rw [if_pos hl, Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)), Parse.bind_ok] at h
        obtain ⟨first, s₁, hf, h⟩ := h
        obtain ⟨hfw, hR₁, hK₁⟩ := ihA _ _ _ (hR.past hs (hR.more hs hne)) hT hf
        rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
        obtain ⟨members, s₂, hm, h⟩ := h
        obtain ⟨hmall, hsize, hR₂, hK₂⟩ := hloop first s₁ _ members s₂ hfw hR₁ (hK₁.target_eq.trans hT) hm
        obtain ⟨y, r₂, hs₂⟩ := hR₂.cons
        rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
        by_cases hamp : y.isPunct "&" = true
        · simp [hamp] at h
        simp only [hamp, hl, Bool.false_eq_true, Bool.true_or, ↓reduceIte, Parse.pure_bind] at h
        rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hunion _ _ (by simpa using hsize) hmall, hR₂, (Kept.past _ _ _).trans (hK₁.trans hK₂)⟩
      · rw [if_neg hl, Parse.pure_bind, Parse.bind_ok] at h
        obtain ⟨first, s₁, hf, h⟩ := h
        obtain ⟨hfw, hR₁, hK₁⟩ := ihA _ _ _ hR hT hf
        rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
        obtain ⟨members, s₂, hm, h⟩ := h
        obtain ⟨hmall, hsize, hR₂, hK₂⟩ := hloop first s₁ _ members s₂ hfw hR₁ (hK₁.target_eq.trans hT) hm
        obtain ⟨y, r₂, hs₂⟩ := hR₂.cons
        rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
        by_cases hamp : y.isPunct "&" = true
        · simp [hamp] at h
        simp only [hamp, hl, Bool.false_eq_true, Bool.false_or, ↓reduceIte, Parse.pure_bind] at h
        by_cases hbig : members.size > 1
        · simp only [hbig, decide_true, ↓reduceIte] at h
          rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
          simp only [Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hunion _ _ (by simpa using hsize) hmall, hR₂, hK₁.trans hK₂⟩
        · simp only [hbig, decide_false, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind, Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨both (arrayWF_wf _ (both_left hfw)) (both_right hfw), hR₂, hK₁.trans hK₂⟩
    · intro s t s' hR hT h
      obtain ⟨x, r, hs⟩ := hR.cons
      simp only [Parse.parseArrayType] at h
      rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.peekAt_rest _ _)] at h
      by_cases hro : (x.isIdent "readonly" && (s.rest[1]?.getD s.eof).isPunct "[" &&
          !(s.rest[1]?.getD s.eof).newlineBefore) = true
      · -- `readonly`, then a tuple.
        rw [if_pos hro] at h
        have hx : x.kind = .ident "readonly" := by simp [Token.isIdent] at hro; exact hro.1.1
        have hne : x.kind ≠ .eof := by rw [hx]; simp
        rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)), Parse.bind_ok] at h
        obtain ⟨inner, s₁, hi, h⟩ := h
        obtain ⟨hiw, hR₂, hK₂⟩ := ihA _ _ _ (hR.past hs (hR.more hs hne)) hT hi
        have hw : Word.ok T [x.kind] = true := hT ▸ hR.tok (by simp [hs]) hne
        cases inner with
        | tuple sp ro elems =>
          cases ro
          · simp only at h
            rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
            simp only [Parse.pure_ok] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨both (by simpa [TypeExpr.arrayWF] using both_left hiw) ?_, hR₂, (Kept.past _ _ _).trans hK₂⟩
            have := WordsOK.cons (T := T) (w := identWord "readonly") (by simpa [identWord, hx] using hw)
              (both_right hiw)
            simpa [TypeExpr.words] using this
          · simp only at h; exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)
        | _ => simp only at h; exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)
      rw [if_neg hro, Parse.pure_bind, Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
      obtain ⟨p, s₁, hp, h⟩ := h
      obtain ⟨hpw, hR₁, hK₁⟩ := ihP _ _ _ hR hT hp
      obtain ⟨h1, -, h2, h3⟩ := (iterate_inv (I := fun a st => (a.arrayWF && a.words.all (Word.ok T)) = true ∧
          a.isReadonlyTuple = false ∧ Ready st ∧ Kept s st)
        (fun a st a' b st' hI hst => by
          obtain ⟨h1, h1w, h2, h3⟩ := arrayStep_inv (T := T) hI.2.2.1 hst
          obtain ⟨h1a, h1r⟩ := h1 (both_left hI.1) hI.2.1
          exact ⟨both h1a (h1w (both_right hI.1)), h1r, h2, hI.2.2.2.trans h3⟩) _ p s₁ t s'
        ⟨both (primaryWF_arrayWF p (both_left hpw)) (both_right hpw), primaryWF_notReadonly p (both_left hpw),
          hR₁, hK₁⟩ h).1
      exact ⟨h1, h2, h3⟩
    · intro s t s' hR hT h
      obtain ⟨x, r, hs⟩ := hR.cons
      simp only [Parse.parsePrimaryType] at h
      rw [Parse.bind_ok] at h
      obtain ⟨t0, s₁, ha, h⟩ := h
      obtain ⟨rfl, hpast⟩ := advance_inv hR hs ha
      -- The word of the first token lexes back.
      have htok : t0.kind ≠ .eof → Word.ok T [t0.kind] = true := fun hne => hT ▸ hR.tok (by simp [hs]) hne
      generalize hk : t0.kind = k at h hpast htok
      cases k with
      | ident name =>
        obtain ⟨rfl, hR₁⟩ := hpast (by simp)
        have hw : Word.ok T (identWord name) = true := htok (by simp)
        simp only at h
        obtain ⟨n, r', hr⟩ := hR₁.cons
        rw [Parse.bind_eq (Parse.peek_eq hr)] at h
        by_cases hdot : n.isPunct "." = true
        · simp [hdot] at h
        simp only [hdot, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind] at h
        by_cases hkw : Parse.keywordTypes.contains name = true
        · simp only [hkw, ↓reduceIte, Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          have hv : (name == "void") = false := by
            cases hn : name == "void"
            · rfl
            · rw [beq_iff_eq] at hn; subst hn; simp [Parse.keywordTypes] at hkw
          exact ⟨both (by simp only [TypeExpr.primaryWF, hkw, Bool.or_true])
            (by simpa [TypeExpr.words, hv] using WordsOK.word hw), hR₁, Kept.past _ _ _⟩
        simp only [hkw, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind] at h
        by_cases hop : Parse.typeOperatorWords.contains name = true
        · rw [if_pos hop] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)
        simp only [hop, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind] at h
        by_cases hrf : Parse.refusedNames.contains name = true
        · rw [if_pos hrf] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)
        simp only [hrf, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind] at h
        have hname : typeName name = true := by
          simp only [typeName, Bool.and_eq_true, Bool.not_eq_true']
          exact ⟨⟨by simpa using hkw, by simpa using hop⟩, by simpa using hrf⟩
        by_cases hlt : (!n.isPunct "<" || n.newlineBefore) = true
        · simp only [hlt, ↓reduceIte, Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨both (by simp [TypeExpr.primaryWF, TypeExpr.allWF, hname])
            (by simpa [TypeExpr.words] using WordsOK.word hw), hR₁, Kept.past _ _ _⟩
        rw [if_neg hlt, Parse.pure_bind] at h
        have hn : n.kind = .punct "<" := by simp [Token.isPunct] at hlt; exact hlt.1
        have hne : n.kind ≠ .eof := by rw [hn]; simp
        rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hr hne)), Parse.bind_eq (Parse.budget_eq _),
          Parse.bind_ok] at h
        obtain ⟨args, s₂, hargs, h⟩ := h
        have hR₂ := hR₁.past hr (hR₁.more hr hne)
        obtain ⟨hall, hR₃, hK₃⟩ := (iterate_inv
          (I := fun a st => (∀ m ∈ a.toList, (m.wf && m.words.all (Word.ok T)) = true) ∧ Ready st ∧
            Kept (past (past s t0 r) n r') st)
          (fun a st a' b st' hI hst => by
            obtain ⟨h1, h2, h3⟩ := typeArgStep_inv ihT hI.2.1 (hI.2.2.target_eq.trans hT) hI.1 hst
            exact ⟨h1, h2, hI.2.2.trans h3⟩) _ #[] _ args s₂ ⟨by simp, hR₂, Kept.refl _⟩ hargs).1
        rw [Parse.bind_ok] at h
        obtain ⟨c, s₄, hc, h⟩ := h
        obtain ⟨_, r₄, _, rfl, hR₄⟩ := expectPunct_inv hR₃ hc
        rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h
        obtain ⟨rfl, rfl⟩ := h
        have hargsw : ∀ m ∈ args.toList, WordsOK T m.words := fun m hm => both_right (hall m hm)
        refine ⟨both (by simp [TypeExpr.primaryWF, hname, (allWF_iff _).mpr fun m hm => both_left (hall m hm)]) ?_,
          hR₄, (Kept.past _ _ _).trans ((Kept.past _ _ _).trans (hK₃.trans (Kept.past _ _ _)))⟩
        cases hal : args.toList with
        | nil => simpa [TypeExpr.words, hal] using WordsOK.word hw
        | cons a as =>
          rw [hal] at hargsw
          simp only [TypeExpr.words]
          exact WordsOK.cons hw (WordsOK.cons (ok_punct (by decide))
            ((WordsOK.separated (sep := ",") (by decide) _ (WordsOK.wordsOf _ hargsw)).append (WordsOK.word (ok_punct (by decide)))))
      | keyword w =>
        obtain ⟨rfl, hR₁⟩ := hpast (by simp)
        by_cases h1 : w = "void"
        · subst h1; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨both (by simp [TypeExpr.primaryWF]) (WordsOK.word (ok_keyword (by decide))), hR₁, Kept.past _ _ _⟩
        by_cases h2 : w = "null"
        · subst h2; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨both (by simp [TypeExpr.primaryWF]) (WordsOK.word (ok_keyword (by decide))), hR₁, Kept.past _ _ _⟩
        by_cases h3 : w = "true"
        · subst h3; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨both (by simp [TypeExpr.primaryWF]) (by
            simpa [TypeExpr.words, LitType.words] using WordsOK.word (T := T) (ok_keyword (w := "true") (by decide))),
            hR₁, Kept.past _ _ _⟩
        by_cases h4 : w = "false"
        · subst h4; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨both (by simp [TypeExpr.primaryWF]) (by
            simpa [TypeExpr.words, LitType.words] using WordsOK.word (T := T) (ok_keyword (w := "false") (by decide))),
            hR₁, Kept.past _ _ _⟩
        simp [h1, h2, h3, h4] at h
      | string v | number v | bigint v =>
        obtain ⟨rfl, hR₁⟩ := hpast (by simp)
        simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨both (by simp [TypeExpr.primaryWF]) (by
          simpa [TypeExpr.words, LitType.words] using WordsOK.word (htok (by simp))), hR₁, Kept.past _ _ _⟩
      | punct p =>
        obtain ⟨rfl, hR₁⟩ := hpast (by simp)
        by_cases hp : p = "("
        · subst hp
          simp only at h
          rw [Parse.bind_ok] at h
          obtain ⟨inner, s₂, hi, h⟩ := h
          obtain ⟨hiw, hR₂, hK₂⟩ := ihT _ _ _ hR₁ hT hi
          rw [Parse.bind_ok] at h
          obtain ⟨c, s₃, hc, h⟩ := h
          obtain ⟨_, r₃, _, rfl, hR₃⟩ := expectPunct_inv hR₂ hc
          rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
          simp only [Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨both (by simpa [TypeExpr.primaryWF] using both_left hiw) (by
            simpa [TypeExpr.words] using WordsOK.cons (ok_punct (by decide))
              ((both_right hiw).append (WordsOK.word (ok_punct (by decide))))), hR₃,
            (Kept.past _ _ _).trans (hK₂.trans (Kept.past _ _ _))⟩
        by_cases hb : p = "["
        · -- A tuple: its elements, and `]`.
          subst hb
          simp only at h
          rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
          obtain ⟨elems, s₂, helems, h⟩ := h
          obtain ⟨⟨hall, hR₃, hK₃⟩, a₁, s₃', -, hlast⟩ := iterate_inv
            (I := fun a st => (∀ m ∈ a.toList, (m.wf && m.words.all (Word.ok T)) = true) ∧ Ready st ∧
              Kept (past s t0 r) st)
            (fun a st a' b st' hI hst => by
              obtain ⟨h1, h2, h3⟩ := typeArgStep_inv ihT hI.2.1 (hI.2.2.target_eq.trans hT) hI.1 hst
              exact ⟨h1, h2, hI.2.2.trans h3⟩) _ #[] _ elems s₂ ⟨by simp, hR₁, Kept.refl _⟩ helems
          have hne' : elems ≠ #[] := by
            obtain ⟨m, hm⟩ := typeArgStep_push hlast
            rw [hm]; simp
          rw [Parse.bind_ok] at h
          obtain ⟨c, s₄, hc, h⟩ := h
          obtain ⟨_, r₄, _, rfl, hR₄⟩ := expectPunct_inv hR₃ hc
          rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
          simp only [Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          have hw : ∀ m ∈ elems.toList, WordsOK T m.words := fun m hm => both_right (hall m hm)
          refine ⟨both ?_ ?_, hR₄, (Kept.past _ _ _).trans (hK₃.trans (Kept.past _ _ _))⟩
          · simp [TypeExpr.primaryWF, hne', (allWF_iff _).mpr fun m hm => both_left (hall m hm)]
          · simp only [TypeExpr.words, Bool.false_eq_true, ↓reduceIte, List.nil_append]
            exact WordsOK.cons (ok_punct (by decide))
              ((WordsOK.separated (sep := ",") (by decide) _ (WordsOK.wordsOf _ hw)).append
                (WordsOK.word (ok_punct (by decide))))
        · simp [hp, hb] at h
      | eof => simp at h

/-! ### The skeleton of a type -/

/-- `s'` is `s` after tokens whose skeleton is `k`. -/
def PastSkel (s s' : ParseState) (k : List TokenKind) : Prop :=
  ∃ src, s.rest = src ++ s'.rest ∧ skel (src.map (·.kind)) = k

theorem PastSkel.refl (s : ParseState) : PastSkel s s [] := ⟨[], rfl, rfl⟩

theorem PastSkel.trans {s₁ s₂ s₃ : ParseState} {a b : List TokenKind} (h₁ : PastSkel s₁ s₂ a)
    (h₂ : PastSkel s₂ s₃ b) : PastSkel s₁ s₃ (a ++ b) := by
  obtain ⟨x, hx, rfl⟩ := h₁
  obtain ⟨y, hy, rfl⟩ := h₂
  exact ⟨x ++ y, by rw [hx, hy, List.append_assoc], by simp [skel_append]⟩

theorem PastSkel.tok {s : ParseState} {x : Token} {r : List Token} (hs : s.rest = x :: r) :
    PastSkel s (past s x r) (skel [x.kind]) := ⟨[x], by simp [hs], rfl⟩

theorem PastSkel.of_eq {s s' : ParseState} {a b : List TokenKind} (h : PastSkel s s' a) (e : a = b) :
    PastSkel s s' b := e ▸ h

/-- The skeletons of `ts`, one after another. -/
def skelsOf (ts : List TypeExpr) : List TokenKind := (ts.map fun t => skel t.tokens).flatten

theorem skel_nonSkel {k : TokenKind} (hk : skelKind k = false) (ks : List TokenKind) : skel (k :: ks) = skel ks := by
  simp [skel, hk]

theorem skel_joined {sep : String} (hsep : skelKind (.punct sep) = false) :
    ∀ xs : List (List TokenKind), skel (joined sep xs) = (xs.map skel).flatten
  | [] => rfl
  | [x] => by simp [joined]
  | x :: y :: xs => by
    simp only [joined, skel_append, skel_nonSkel hsep, List.map_cons, List.flatten_cons]
    rw [skel_joined hsep (y :: xs)]
    simp

theorem skel_bars : ∀ ts : List TypeExpr,
    skel (ts.map fun i => .punct "|" :: i.tokens).flatten = skelsOf ts
  | [] => rfl
  | t :: ts => by
    simp only [List.map_cons, List.flatten_cons, skel_append, skel_nonSkel (k := .punct "|") rfl, skel_bars ts,
      skelsOf]

theorem skel_union (sp : Span) : ∀ ms : List TypeExpr, skel (TypeExpr.union sp ms).tokens = skelsOf ms
  | [] => rfl
  | [m] => by rw [tokens_union_one, skel_nonSkel rfl]; simp [skelsOf]
  | m₁ :: m₂ :: ms => by
    rw [tokens_union, skel_append, skel_bars]; simp [skelsOf]

theorem skel_ref (sp : Span) (n : String) (args : List TypeExpr) (h : args ≠ []) :
    skel (TypeExpr.ref sp n args).tokens = skelsOf args ++ [.punct ">"] := by
  rw [tokens_ref sp n args h, skel_append, skel_nonSkel (k := .ident n) rfl,
    skel_nonSkel (k := .punct "<") rfl, skel_joined (sep := ",") rfl]
  simp only [skelsOf, List.map_map, Function.comp_def]
  rfl

theorem skel_tuple (sp : Span) (es : List TypeExpr) :
    skel (TypeExpr.tuple sp false es).tokens = .punct "[" :: skelsOf es ++ [.punct "]"] := by
  have hj : skel (joined "," (es.map TypeExpr.tokens)) = skelsOf es := by
    rw [skel_joined (sep := ",") rfl]; simp [skelsOf, List.map_map, Function.comp_def]
  rw [tokens_tuple]
  simp only [skel] at hj ⊢
  simp [List.filter_append, skelKind, hj]

theorem skelsOf_push (a : Array TypeExpr) (m : TypeExpr) :
    skelsOf (a.push m).toList = skelsOf a.toList ++ skel m.tokens := by
  simp [skelsOf]

/-- What `p` gives when it reads a type: a state that is still ready, past the
skeleton of the type's printed tokens. -/
def SkelT (p : ParseM TypeExpr) : Prop :=
  ∀ s t s', Ready s → p s = .ok t s' → Ready s' ∧ PastSkel s s' (skel t.tokens)

theorem arrayStep_skel {start : Pos} {a a' : TypeExpr} {b : Bool} {s s' : ParseState}
    (hR : Ready s) (h : Parse.arrayStep start a s = .ok (a', b) s') :
    Ready s' ∧ ∃ k, PastSkel s s' k ∧ skel a'.tokens = skel a.tokens ++ k := by
  have hR' := (arrayStep_inv (T := s.target) hR h).2.2.1
  refine ⟨hR', ?_⟩
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.arrayStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : (!x.isPunct "[" || x.newlineBefore) = true
  · rw [if_pos hc] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨[], PastSkel.refl _, by simp⟩
  · rw [if_neg hc] at h
    have hx : x.kind = .punct "[" := by simp [Token.isPunct] at hc; exact hc.1
    have hr := hR.more hs (by rw [hx]; simp)
    obtain ⟨y, r', rfl⟩ := List.exists_cons_of_ne_nil hr
    rw [Parse.pure_bind, Parse.bind_eq (Parse.peekAt_eq (k := 1) (t := y) (by simp [hs]))] at h
    by_cases hy : y.isPunct "]" = true
    · have hyk : y.kind = .punct "]" := by simpa [Token.isPunct] using hy
      have hR₁ := hR.past hs hr
      simp only [hy, ↓reduceIte] at h
      rw [Parse.pure_bind, Parse.bind_eq (skip_two hs (hR₁.more rfl (by rw [hyk]; simp))),
        Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, _⟩, rfl⟩ := h
      refine ⟨_, (PastSkel.tok hs).trans (PastSkel.tok (s := past s x (y :: r')) rfl), ?_⟩
      rw [TypeExpr.tokens_array, skel_append, hx, hyk]
      rfl
    · simp only [hy, Bool.false_eq_true, ↓reduceIte] at h
      rw [Parse.bind_ok] at h
      obtain ⟨_, _, hf, _⟩ := h
      exact absurd hf (Parse.failAt_ne_ok _ _ _ _ _)

theorem unionStep_skel {p : ParseM TypeExpr} (hp : SkelT p) {a a' : Array TypeExpr} {b : Bool}
    {s s' : ParseState} (hR : Ready s) (h : Parse.unionStep p a s = .ok (a', b) s') :
    Ready s' ∧ (a' = a ∨ ∃ m, a' = a.push m) ∧ ∃ k, PastSkel s s' k ∧ skelsOf a'.toList = skelsOf a.toList ++ k := by
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.unionStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hx : x.isPunct "|" = true
  · have hk : x.kind = .punct "|" := by simpa [Token.isPunct] using hx
    have hne : x.kind ≠ .eof := by rw [hk]; simp
    rw [if_neg (by simp [hx]), Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)),
      Parse.bind_ok] at h
    obtain ⟨m, s₁, hm, h⟩ := h
    obtain ⟨hR₁, hP⟩ := hp _ _ _ (hR.past hs (hR.more hs hne)) hm
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    refine ⟨hR₁, .inr ⟨m, rfl⟩, _, (PastSkel.tok hs).trans hP, ?_⟩
    rw [skelsOf_push, hk, skel_nonSkel rfl]; rfl
  · rw [if_pos (by simp [hx])] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR, .inl rfl, [], PastSkel.refl _, by simp⟩

theorem typeArgStep_skel {p : ParseM TypeExpr} (hp : SkelT p) {a a' : Array TypeExpr} {b : Bool}
    {s s' : ParseState} (hR : Ready s) (h : Parse.typeArgStep p a s = .ok (a', b) s') :
    Ready s' ∧ (∃ m, a' = a.push m) ∧ ∃ k, PastSkel s s' k ∧ skelsOf a'.toList = skelsOf a.toList ++ k := by
  simp only [Parse.typeArgStep] at h
  rw [Parse.bind_ok] at h
  obtain ⟨m, s₁, hm, h⟩ := h
  obtain ⟨hR₁, hP⟩ := hp _ _ _ hR hm
  obtain ⟨x, r, hs⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hx : x.isPunct "," = true
  · have hk : x.kind = .punct "," := by simpa [Token.isPunct] using hx
    have hne : x.kind ≠ .eof := by rw [hk]; simp
    rw [if_neg (by simp [hx]), Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hs hne))] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    refine ⟨hR₁.past hs (hR₁.more hs hne), ⟨m, rfl⟩, _, hP.trans (PastSkel.tok hs), ?_⟩
    rw [skelsOf_push, hk]
    simp [skel, skelKind]
  · rw [if_pos (by simp [hx])] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR₁, ⟨m, rfl⟩, _, hP, by rw [skelsOf_push]⟩

theorem keywordType_skel (name : String) : skel (TypeExpr.keyword sp name).tokens = [] := by
  simp only [TypeExpr.tokens, TypeExpr.words]; split <;> simp [keywordWord, identWord, skel, skelKind]

/-- The type parser reads tokens with the skeleton of the printed type. -/
theorem types_skel : ∀ f : Nat,
    SkelT (Parse.parseType f) ∧ SkelT (Parse.parseArrayType f) ∧ SkelT (Parse.parsePrimaryType f)
  | 0 => ⟨fun _ _ _ _ h => absurd h (by simp only [Parse.parseType]; exact outOfFuel_ne_ok _ _ _),
      fun _ _ _ _ h => absurd h (by simp only [Parse.parseArrayType]; exact outOfFuel_ne_ok _ _ _),
      fun _ _ _ _ h => absurd h (by simp only [Parse.parsePrimaryType]; exact outOfFuel_ne_ok _ _ _)⟩
  | f + 1 => by
    obtain ⟨ihT, ihA, ihP⟩ := types_skel f
    refine ⟨?_, ?_, ?_⟩
    · intro s t s' hR h
      obtain ⟨x, r, hs⟩ := hR.cons
      simp only [Parse.parseType] at h
      rw [Parse.bind_eq (Parse.peek_eq hs)] at h
      -- The loop over the members after the first.
      have hloop : ∀ (first : TypeExpr) (s₀ s₁ : ParseState) (n : Nat) (members : Array TypeExpr) (s₂ : ParseState),
          Ready s₁ → PastSkel s₀ s₁ (skel first.tokens) →
          Parse.iterate n #[first] (Parse.unionStep (Parse.parseArrayType f)) s₁ = .ok members s₂ →
          Ready s₂ ∧ PastSkel s₀ s₂ (skelsOf members.toList) ∧ ∃ rest, members.toList = first :: rest :=
        fun first s₀ s₁ n members s₂ hR₁ hP₁ hm => (iterate_inv
          (I := fun a st => Ready st ∧ PastSkel s₀ st (skelsOf a.toList) ∧ ∃ rest, a.toList = first :: rest)
          (fun a st a' b st' hI hst => by
            obtain ⟨h1, h2, k, h3, h4⟩ := unionStep_skel ihA hI.1 hst
            refine ⟨h1, (hI.2.1.trans h3).of_eq h4.symm, ?_⟩
            obtain ⟨rest, hrest⟩ := hI.2.2
            rcases h2 with rfl | ⟨m, rfl⟩
            · exact ⟨rest, hrest⟩
            · exact ⟨rest ++ [m], by simp [hrest]⟩) _ _ _ _ _
          ⟨hR₁, hP₁.of_eq (by simp [skelsOf]), [], rfl⟩ hm).1
      by_cases hl : x.isPunct "|" = true
      · have hk : x.kind = .punct "|" := by simpa [Token.isPunct] using hl
        have hne : x.kind ≠ .eof := by rw [hk]; simp
        rw [if_pos hl, Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)), Parse.bind_ok] at h
        obtain ⟨first, s₁, hf, h⟩ := h
        obtain ⟨hR₁, hP₁⟩ := ihA _ _ _ (hR.past hs (hR.more hs hne)) hf
        rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
        obtain ⟨members, s₂, hm, h⟩ := h
        obtain ⟨hR₂, hP₂, _⟩ := hloop first _ s₁ _ members s₂ hR₁ hP₁ hm
        obtain ⟨y, r₂, hs₂⟩ := hR₂.cons
        rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
        by_cases hamp : y.isPunct "&" = true
        · simp [hamp] at h
        simp only [hamp, hl, Bool.false_eq_true, Bool.true_or, ↓reduceIte, Parse.pure_bind] at h
        rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hR₂, ((PastSkel.tok hs).trans hP₂).of_eq (by rw [skel_union, hk, skel_nonSkel rfl]; rfl)⟩
      · rw [if_neg hl, Parse.pure_bind, Parse.bind_ok] at h
        obtain ⟨first, s₁, hf, h⟩ := h
        obtain ⟨hR₁, hP₁⟩ := ihA _ _ _ hR hf
        rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
        obtain ⟨members, s₂, hm, h⟩ := h
        obtain ⟨hR₂, hP₂, rest, hrest⟩ := hloop first _ s₁ _ members s₂ hR₁ hP₁ hm
        obtain ⟨y, r₂, hs₂⟩ := hR₂.cons
        rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
        by_cases hamp : y.isPunct "&" = true
        · simp [hamp] at h
        simp only [hamp, hl, Bool.false_eq_true, Bool.false_or, ↓reduceIte, Parse.pure_bind] at h
        by_cases hbig : members.size > 1
        · simp only [hbig, decide_true, ↓reduceIte] at h
          rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
          simp only [Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hR₂, hP₂.of_eq (by rw [skel_union])⟩
        · simp only [hbig, decide_false, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind, Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          have hnil : rest = [] := by
            have := congrArg List.length hrest
            simp at this; cases rest with
            | nil => rfl
            | cons _ _ => simp at this; omega
          subst hnil
          exact ⟨hR₂, hP₂.of_eq (by rw [hrest]; simp [skelsOf])⟩
    · intro s t s' hR h
      simp only [Parse.parseArrayType] at h
      obtain ⟨x, r, hs⟩ := hR.cons
      rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.peekAt_rest _ _)] at h
      by_cases hro : (x.isIdent "readonly" && (s.rest[1]?.getD s.eof).isPunct "[" &&
          !(s.rest[1]?.getD s.eof).newlineBefore) = true
      · rw [if_pos hro] at h
        have hx : x.kind = .ident "readonly" := by simp [Token.isIdent] at hro; exact hro.1.1
        have hne : x.kind ≠ .eof := by rw [hx]; simp
        rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)), Parse.bind_ok] at h
        obtain ⟨inner, s₁, hi, h⟩ := h
        obtain ⟨hR₁, hP₁⟩ := ihA _ _ _ (hR.past hs (hR.more hs hne)) hi
        cases inner with
        | tuple sp ro elems =>
          cases ro
          · simp only at h
            rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
            simp only [Parse.pure_ok] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨hR₁, ((PastSkel.tok hs).trans hP₁).of_eq ?_⟩
            rw [tokens_readonly, hx]
            simp [skel, skelKind]
            rfl
          · simp only at h; exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)
        | _ => simp only at h; exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)
      rw [if_neg hro, Parse.pure_bind, Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
      obtain ⟨p, s₁, hp, h⟩ := h
      obtain ⟨hR₁, hP₁⟩ := ihP _ _ _ hR hp
      exact (iterate_inv (I := fun a st => Ready st ∧ PastSkel s st (skel a.tokens))
        (fun a st a' b st' hI hst => by
          obtain ⟨h1, k, h2, h3⟩ := arrayStep_skel hI.1 hst
          exact ⟨h1, (hI.2.trans h2).of_eq h3.symm⟩) _ p s₁ t s' ⟨hR₁, hP₁⟩ h).1
    · intro s t s' hR h
      obtain ⟨x, r, hs⟩ := hR.cons
      simp only [Parse.parsePrimaryType] at h
      rw [Parse.bind_ok] at h
      obtain ⟨t0, s₁, ha, h⟩ := h
      obtain ⟨rfl, hpast⟩ := advance_inv hR hs ha
      generalize hk : t0.kind = k at h hpast
      cases k with
      | ident name =>
        obtain ⟨rfl, hR₁⟩ := hpast (by simp)
        have hP₁ : PastSkel s (past s t0 r) [] := (PastSkel.tok hs).of_eq (by rw [hk]; rfl)
        simp only at h
        obtain ⟨n, r', hr⟩ := hR₁.cons
        rw [Parse.bind_eq (Parse.peek_eq hr)] at h
        by_cases hdot : n.isPunct "." = true
        · simp [hdot] at h
        simp only [hdot, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind] at h
        by_cases hkw : Parse.keywordTypes.contains name = true
        · simp only [hkw, ↓reduceIte, Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hR₁, hP₁.of_eq (keywordType_skel name).symm⟩
        simp only [hkw, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind] at h
        by_cases hop : Parse.typeOperatorWords.contains name = true
        · rw [if_pos hop] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)
        simp only [hop, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind] at h
        by_cases hrf : Parse.refusedNames.contains name = true
        · rw [if_pos hrf] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)
        simp only [hrf, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind] at h
        by_cases hlt : (!n.isPunct "<" || n.newlineBefore) = true
        · simp only [hlt, ↓reduceIte, Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hR₁, hP₁.of_eq (by simp [TypeExpr.tokens, TypeExpr.words, identWord, skel, skelKind])⟩
        rw [if_neg hlt, Parse.pure_bind] at h
        have hn : n.kind = .punct "<" := by simp [Token.isPunct] at hlt; exact hlt.1
        have hne : n.kind ≠ .eof := by rw [hn]; simp
        rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hr hne)), Parse.bind_eq (Parse.budget_eq _),
          Parse.bind_ok] at h
        obtain ⟨args, s₂, hargs, h⟩ := h
        have hR₂ := hR₁.past hr (hR₁.more hr hne)
        have hP₂ : PastSkel s (past (past s t0 r) n r') [] :=
          (hP₁.trans (PastSkel.tok hr)).of_eq (by rw [hn]; rfl)
        obtain ⟨⟨hR₃, hP₃⟩, a₁, s₃', hI₁, hlast⟩ := iterate_inv (σ := Array TypeExpr)
          (I := fun a st => Ready st ∧ PastSkel s st (skelsOf a.toList))
          (fun a st a' b st' hI hst => by
            obtain ⟨h1, _, k, h2, h3⟩ := typeArgStep_skel ihT hI.1 hst
            exact ⟨h1, (hI.2.trans h2).of_eq h3.symm⟩) _ #[] _ args s₂ ⟨hR₂, hP₂.of_eq (by simp [skelsOf])⟩ hargs
        have hne' : args.toList ≠ [] := by
          obtain ⟨_, ⟨m, rfl⟩, _⟩ := typeArgStep_skel ihT hI₁.1 hlast
          simp
        rw [Parse.bind_ok] at h
        obtain ⟨c, s₄, hc, h⟩ := h
        obtain ⟨hck, r₄, hs₄, rfl, hR₄⟩ := expectPunct_inv hR₃ hc
        rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hR₄, (hP₃.trans (PastSkel.tok hs₄)).of_eq (by rw [skel_ref _ _ _ hne', hck]; rfl)⟩
      | keyword w =>
        obtain ⟨rfl, hR₁⟩ := hpast (by simp)
        have hP₁ : PastSkel s (past s t0 r) [] := (PastSkel.tok hs).of_eq (by rw [hk]; rfl)
        by_cases h1 : w = "void"
        · subst h1; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨hR₁, hP₁.of_eq (keywordType_skel _).symm⟩
        by_cases h2 : w = "null"
        · subst h2; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨hR₁, hP₁.of_eq (by simp [TypeExpr.tokens, TypeExpr.words, keywordWord, skel, skelKind])⟩
        by_cases h3 : w = "true"
        · subst h3; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨hR₁, hP₁.of_eq (by simp [TypeExpr.tokens, TypeExpr.words, LitType.words, keywordWord, skel, skelKind])⟩
        by_cases h4 : w = "false"
        · subst h4; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨hR₁, hP₁.of_eq (by simp [TypeExpr.tokens, TypeExpr.words, LitType.words, keywordWord, skel, skelKind])⟩
        simp [h1, h2, h3, h4] at h
      | string v | number v | bigint v =>
        obtain ⟨rfl, hR₁⟩ := hpast (by simp)
        have hP₁ : PastSkel s (past s t0 r) [] := (PastSkel.tok hs).of_eq (by rw [hk]; rfl)
        simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨hR₁, hP₁.of_eq (by simp [TypeExpr.tokens, TypeExpr.words, LitType.words, skel, skelKind])⟩
      | punct p =>
        obtain ⟨rfl, hR₁⟩ := hpast (by simp)
        by_cases hp : p = "("
        · subst hp
          simp only at h
          rw [Parse.bind_ok] at h
          obtain ⟨inner, s₂, hi, h⟩ := h
          obtain ⟨hR₂, hP₂⟩ := ihT _ _ _ hR₁ hi
          rw [Parse.bind_ok] at h
          obtain ⟨c, s₃, hc, h⟩ := h
          obtain ⟨hck, r₃, hs₃, rfl, hR₃⟩ := expectPunct_inv hR₂ hc
          rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
          simp only [Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hR₃, (((PastSkel.tok hs).trans hP₂).trans (PastSkel.tok hs₃)).of_eq (by
            rw [TypeExpr.tokens_paren, hk, hck]; simp [skel, skelKind])⟩
        by_cases hb : p = "["
        · subst hb
          simp only at h
          rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
          obtain ⟨elems, s₂, helems, h⟩ := h
          have hP₁ : PastSkel s (past s t0 r) [.punct "["] := (PastSkel.tok hs).of_eq (by rw [hk]; rfl)
          obtain ⟨⟨hR₃, hP₃⟩, -⟩ := iterate_inv (σ := Array TypeExpr)
            (I := fun a st => Ready st ∧ PastSkel s st (.punct "[" :: skelsOf a.toList))
            (fun a st a' b st' hI hst => by
              obtain ⟨h1, _, k, h2, h3⟩ := typeArgStep_skel ihT hI.1 hst
              exact ⟨h1, (hI.2.trans h2).of_eq (by rw [h3]; simp)⟩) _ #[] _ elems s₂
            ⟨hR₁, hP₁.of_eq (by simp [skelsOf])⟩ helems
          rw [Parse.bind_ok] at h
          obtain ⟨c, s₄, hc, h⟩ := h
          obtain ⟨hck, r₄, hs₄, rfl, hR₄⟩ := expectPunct_inv hR₃ hc
          rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
          simp only [Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hR₄, (hP₃.trans (PastSkel.tok hs₄)).of_eq (by rw [skel_tuple, hck]; simp [skel, skelKind])⟩
        · simp [hp, hb] at h
      | eof => simp at h

/-! ### Operators -/

theorem skip_inv {s s' : ParseState} {a r : List Token} (h : Ready s) (hs : s.rest = a ++ r) (hr : r ≠ [])
    (hk : Parse.skip a.length s = .ok () s') : s'.rest = r ∧ Ready s' ∧ Kept s s' := by
  obtain ⟨s'', h1, hL⟩ := Parse.skip_ok a hs hr h.1.2
  obtain ⟨_, rfl⟩ := ok_unique hk h1
  have hK : Kept s s' := ⟨hL.eof_eq, hL.inFunction_eq, hL.loopDepth_eq, hL.target_eq⟩
  exact ⟨hL.rest_eq, h.suffix (by rw [hs, hL.rest_eq]) (by rw [hL.rest_eq]; exact hr)
    (by rw [hL.left_eq, hL.rest_eq]) hL.eof_eq hL.target_eq, hK⟩

/-- A peeked token that is not the end of the file is a token of the state. -/
theorem peekAt_real {s : ParseState} {k : Nat} (h : Ready s) (hk : (s.rest[k]?.getD s.eof).kind ≠ .eof) :
    ∃ t, s.rest[k]? = some t ∧ s.rest[k]?.getD s.eof = t := by
  cases hr : s.rest[k]? with
  | none => rw [hr] at hk; exact absurd h.2.2.1 hk
  | some t => exact ⟨t, rfl, rfl⟩

theorem ofSymbol_binOp {s : String} {op : BinOp} (h : BinOp.ofSymbol? s = some op) : op.symbol = s := by
  have := List.find?_some h
  simpa using this

theorem ofSymbol_assignOp {s : String} {op : AssignOp} (h : AssignOp.ofSymbol? s = some op) : op.symbol = s := by
  have := List.find?_some h
  simpa using this

/-- An operator of one punctuator token, other than `>`, is that token. -/
theorem symbol_binOp_punct {op : BinOp} (hl : Lex.punctuators.contains op.symbol = true)
    (hgt : op.symbol ≠ ">") : symbol op.symbol = [.punct op.symbol] := by
  cases op <;> simp_all (config := { decide := true }) [symbol, BinOp.symbol, punctWord]

/-- A token that is not the end of the file is not the last token. -/
theorem Ready.notLast {s : ParseState} {a r : List Token} {x : Token} (h : Ready s) (hs : s.rest = a ++ x :: r)
    (hx : x.kind ≠ .eof) : r ≠ [] := by
  rintro rfl
  have := h.2.1
  rw [hs, List.getLast?_append] at this
  simp at this
  exact hx (this ▸ h.2.2.1)

/-- What `peekGreater` gives, from the tokens it peeks at. -/
def greaterOf (t0 t1 t2 t3 : Token) : String × Nat :=
  let touches (a b : Token) : Bool := b.span.start == a.span.stop
  if t1.isPunct ">" && touches t0 t1 then
    if t2.isPunct ">" && touches t1 t2 then
      if t3.isPunct "=" && touches t2 t3 then (">>>=", 4) else (">>>", 3)
    else if t2.isPunct "=" && touches t1 t2 then (">>=", 3) else (">>", 2)
  else if t1.isPunct "=" && touches t0 t1 then (">=", 2) else (">", 1)

theorem peekGreater_eq (s : ParseState) : Parse.peekGreater s =
    .ok (greaterOf (s.rest[0]?.getD s.eof) (s.rest[1]?.getD s.eof) (s.rest[2]?.getD s.eof)
      (s.rest[3]?.getD s.eof)) s := by
  simp only [Parse.peekGreater, greaterOf]
  rw [Parse.bind_eq (Parse.peekAt_rest s 0), Parse.bind_eq (Parse.peekAt_rest s 1),
    Parse.bind_eq (Parse.peekAt_rest s 2), Parse.bind_eq (Parse.peekAt_rest s 3)]
  split <;> (try split) <;> (try split) <;> rfl

/-- A peeked token of kind `punct p` is a token of the state. -/
theorem peek_punct {s : ParseState} (h : Ready s) {k : Nat} {p : String}
    (hk : (s.rest[k]?.getD s.eof).isPunct p = true) : ∃ t, s.rest[k]? = some t ∧ t.kind = .punct p := by
  have hk' : (s.rest[k]?.getD s.eof).kind = .punct p := by simpa [Token.isPunct] using hk
  obtain ⟨t, ht, hteq⟩ := peekAt_real h (by rw [hk']; simp)
  exact ⟨t, ht, by rw [← hteq]; exact hk'⟩

theorem list_two {l : List Token} {a b : Token} (h0 : l[0]? = some a) (h1 : l[1]? = some b) :
    ∃ r, l = a :: b :: r := by
  match l, h0, h1 with
  | a' :: b' :: r, h0, h1 => simp at h0 h1; subst h0; subst h1; exact ⟨r, rfl⟩

theorem list_three {l : List Token} {a b c : Token} (h0 : l[0]? = some a) (h1 : l[1]? = some b)
    (h2 : l[2]? = some c) : ∃ r, l = a :: b :: c :: r := by
  match l, h0, h1, h2 with
  | a' :: b' :: c' :: r, h0, h1, h2 => simp at h0 h1 h2; subst h0; subst h1; subst h2; exact ⟨r, rfl⟩

theorem list_four {l : List Token} {a b c d : Token} (h0 : l[0]? = some a) (h1 : l[1]? = some b)
    (h2 : l[2]? = some c) (h3 : l[3]? = some d) : ∃ r, l = a :: b :: c :: d :: r := by
  match l, h0, h1, h2, h3 with
  | a' :: b' :: c' :: d' :: r, h0, h1, h2, h3 =>
    simp at h0 h1 h2 h3; subst h0; subst h1; subst h2; subst h3; exact ⟨r, rfl⟩

/-- `peekGreater` gives an operator whose tokens come first. -/
theorem greater_inv {s : ParseState} {x : Token} {r : List Token} {sym : String} {w : Nat} (h : Ready s)
    (hs : s.rest = x :: r) (hx : x.kind = .punct ">")
    (hg : greaterOf (s.rest[0]?.getD s.eof) (s.rest[1]?.getD s.eof) (s.rest[2]?.getD s.eof)
      (s.rest[3]?.getD s.eof) = (sym, w)) :
    ∃ a r', s.rest = a ++ r' ∧ a.length = w ∧ a.map (·.kind) = symbol sym ∧ r' ≠ [] := by
  have h0 : s.rest[0]? = some x := by simp [hs]
  unfold greaterOf at hg
  dsimp only at hg
  split at hg
  · rename_i c1
    obtain ⟨y, hy, hyk⟩ := peek_punct h (by simp only [Bool.and_eq_true] at c1; exact c1.1)
    split at hg
    · rename_i c2
      obtain ⟨z, hz, hzk⟩ := peek_punct h (by simp only [Bool.and_eq_true] at c2; exact c2.1)
      split at hg
      · rename_i c3
        obtain ⟨u, hu, huk⟩ := peek_punct h (by simp only [Bool.and_eq_true] at c3; exact c3.1)
        obtain ⟨r', hr'⟩ := list_four h0 hy hz hu
        simp only [Prod.mk.injEq] at hg; obtain ⟨rfl, rfl⟩ := hg
        exact ⟨[x, y, z, u], r', by simpa using hr', rfl,
          by simp (config := { decide := true }) [hx, hyk, hzk, huk, symbol],
          h.notLast (a := [x, y, z]) (by simpa using hr') (by rw [huk]; simp)⟩
      · obtain ⟨r', hr'⟩ := list_three h0 hy hz
        simp only [Prod.mk.injEq] at hg; obtain ⟨rfl, rfl⟩ := hg
        exact ⟨[x, y, z], r', by simpa using hr', rfl,
          by simp (config := { decide := true }) [hx, hyk, hzk, symbol],
          h.notLast (a := [x, y]) (by simpa using hr') (by rw [hzk]; simp)⟩
    · split at hg
      · rename_i c2
        obtain ⟨z, hz, hzk⟩ := peek_punct h (by simp only [Bool.and_eq_true] at c2; exact c2.1)
        obtain ⟨r', hr'⟩ := list_three h0 hy hz
        simp only [Prod.mk.injEq] at hg; obtain ⟨rfl, rfl⟩ := hg
        exact ⟨[x, y, z], r', by simpa using hr', rfl,
          by simp (config := { decide := true }) [hx, hyk, hzk, symbol],
          h.notLast (a := [x, y]) (by simpa using hr') (by rw [hzk]; simp)⟩
      · obtain ⟨r', hr'⟩ := list_two h0 hy
        simp only [Prod.mk.injEq] at hg; obtain ⟨rfl, rfl⟩ := hg
        exact ⟨[x, y], r', by simpa using hr', rfl,
          by simp (config := { decide := true }) [hx, hyk, symbol],
          h.notLast (a := [x]) (by simpa using hr') (by rw [hyk]; simp)⟩
  · split at hg
    · rename_i c1
      obtain ⟨y, hy, hyk⟩ := peek_punct h (by simp only [Bool.and_eq_true] at c1; exact c1.1)
      obtain ⟨r', hr'⟩ := list_two h0 hy
      simp only [Prod.mk.injEq] at hg; obtain ⟨rfl, rfl⟩ := hg
      exact ⟨[x, y], r', by simpa using hr', rfl,
        by simp (config := { decide := true }) [hx, hyk, symbol],
        h.notLast (a := [x]) (by simpa using hr') (by rw [hyk]; simp)⟩
    · simp only [Prod.mk.injEq] at hg; obtain ⟨rfl, rfl⟩ := hg
      exact ⟨[x], r, by simpa using hs, rfl, by simp (config := { decide := true }) [hx, symbol],
        h.more hs (by rw [hx]; simp)⟩

/-- `peekBinaryOp` changes nothing, and it gives an operator whose tokens come first. -/
theorem peekBinaryOp_inv {s s' : ParseState} {v : Option (BinOp × Nat)} (h : Ready s)
    (hp : Parse.peekBinaryOp s = .ok v s') : s' = s ∧ ∀ op w, v = some (op, w) →
      ∃ a r, s.rest = a ++ r ∧ a.length = w ∧ a.map (·.kind) = symbol op.symbol ∧ r ≠ [] := by
  obtain ⟨x, r, hs⟩ := h.cons
  have hlex : x.kind = .eof ∨ TokenKind.ok s.target x.kind = true := h.2.2.2 x (by simp [hs])
  simp only [Parse.peekBinaryOp] at hp
  rw [Parse.bind_eq (Parse.peek_eq hs)] at hp
  generalize hk : x.kind = k at hp hlex
  cases k with
  | keyword kw =>
    by_cases h1 : kw = "in"
    · subst h1
      simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨rfl, fun op w he => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨[x], r, by simpa using hs, rfl,
        by simp (config := { decide := true }) [hk, symbol, BinOp.symbol, keywordWord],
        h.more hs (by rw [hk]; simp)⟩
    by_cases h2 : kw = "instanceof"
    · subst h2
      simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨rfl, fun op w he => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨[x], r, by simpa using hs, rfl,
        by simp (config := { decide := true }) [hk, symbol, BinOp.symbol, keywordWord],
        h.more hs (by rw [hk]; simp)⟩
    simp [h1, h2] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨rfl, fun _ _ he => by simp at he⟩
  | punct p =>
    by_cases hg : p = ">"
    · subst hg
      simp only at hp
      rw [Parse.bind_eq (peekGreater_eq s)] at hp
      generalize hgo : greaterOf _ _ _ _ = gw at hp
      obtain ⟨sym, wd⟩ := gw
      simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨rfl, fun op w he => ?_⟩
      obtain ⟨op', hop', heq⟩ := Option.map_eq_some_iff.mp he
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨a, r', h1, h2, h3, h4⟩ := greater_inv h hs hk hgo
      exact ⟨a, r', h1, h2, by rw [ofSymbol_binOp hop']; exact h3, h4⟩
    · simp only at hp
      simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨rfl, fun op w he => ?_⟩
      obtain ⟨op', hop', heq⟩ := Option.map_eq_some_iff.mp he
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      have hsym := ofSymbol_binOp hop'
      have hl : Lex.punctuators.contains op'.symbol = true := by
        rw [hsym]; simpa [TokenKind.ok] using hlex
      exact ⟨[x], r, by simpa using hs, rfl, by rw [symbol_binOp_punct hl (by rw [hsym]; exact hg), hsym]; simp [hk],
        h.more hs (by rw [hk]; simp)⟩
  | _ =>
    simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
    exact ⟨rfl, fun _ _ he => by simp at he⟩

theorem symbol_assignOp_punct {op : AssignOp} (hl : Lex.punctuators.contains op.symbol = true)
    (hgt : op.symbol ≠ ">") : symbol op.symbol = [.punct op.symbol] := by
  cases op <;> simp_all (config := { decide := true }) [symbol, AssignOp.symbol,
    punctWord]

/-- `peekAssignOp` changes nothing, and it gives an operator whose tokens come first. -/
theorem peekAssignOp_inv {s s' : ParseState} {v : Option (AssignOp × Nat)} (h : Ready s)
    (hp : Parse.peekAssignOp s = .ok v s') : s' = s ∧ ∀ op w, v = some (op, w) →
      ∃ a r, s.rest = a ++ r ∧ a.length = w ∧ a.map (·.kind) = symbol op.symbol ∧ r ≠ [] := by
  obtain ⟨x, r, hs⟩ := h.cons
  have hlex : x.kind = .eof ∨ TokenKind.ok s.target x.kind = true := h.2.2.2 x (by simp [hs])
  simp only [Parse.peekAssignOp] at hp
  rw [Parse.bind_eq (Parse.peek_eq hs)] at hp
  generalize hk : x.kind = k at hp hlex
  cases k with
  | punct p =>
    by_cases hg : p = ">"
    · subst hg
      simp only at hp
      rw [Parse.bind_eq (peekGreater_eq s)] at hp
      generalize hgo : greaterOf _ _ _ _ = gw at hp
      obtain ⟨sym, wd⟩ := gw
      simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨rfl, fun op w he => ?_⟩
      obtain ⟨op', hop', heq⟩ := Option.map_eq_some_iff.mp he
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨a, r', h1, h2, h3, h4⟩ := greater_inv h hs hk hgo
      exact ⟨a, r', h1, h2, by rw [ofSymbol_assignOp hop']; exact h3, h4⟩
    · simp only at hp
      simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨rfl, fun op w he => ?_⟩
      obtain ⟨op', hop', heq⟩ := Option.map_eq_some_iff.mp he
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      have hsym := ofSymbol_assignOp hop'
      have hl : Lex.punctuators.contains op'.symbol = true := by
        rw [hsym]; simpa [TokenKind.ok] using hlex
      exact ⟨[x], r, by simpa using hs, rfl,
        by rw [symbol_assignOp_punct hl (by rw [hsym]; exact hg), hsym]; simp [hk],
        h.more hs (by rw [hk]; simp)⟩
  | _ =>
    simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
    exact ⟨rfl, fun _ _ he => by simp at he⟩

/-- A unary operator is the one token of its symbol. -/
theorem unaryOp_inv {t : Token} {op : UnaryOp} (h : Parse.unaryOp? t = some op) : [t.kind] = symbol op.symbol := by
  unfold Parse.unaryOp? at h
  generalize hk : t.kind = k at h
  cases k with
  | punct p =>
    by_cases h1 : p = "!"; · subst h1; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, punctWord]
    by_cases h2 : p = "-"; · subst h2; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, punctWord]
    by_cases h3 : p = "+"; · subst h3; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, punctWord]
    by_cases h4 : p = "~"; · subst h4; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, punctWord]
    simp [h1, h2, h3, h4] at h
  | keyword w =>
    by_cases h1 : w = "typeof"; · subst h1; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, keywordWord]
    by_cases h2 : w = "void"; · subst h2; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, keywordWord]
    simp [h1, h2] at h
  | _ => simp at h

theorem updateOp_inv {t : Token} {op : UpdateOp} (h : Parse.updateOp? t = some op) : t.kind = .punct op.symbol := by
  unfold Parse.updateOp? at h
  by_cases h1 : t.isPunct "++" = true
  · simp [h1] at h; subst h; simpa [Token.isPunct, UpdateOp.symbol] using h1
  · by_cases h2 : t.isPunct "--" = true
    · simp [h1, h2] at h; subst h; simpa [Token.isPunct, UpdateOp.symbol] using h2
    · simp [h1, h2] at h

theorem get_bind {α : Type} {f : ParseState → ParseM α} {s : ParseState} :
    ((get : ParseM ParseState) >>= f) s = f s s := by
  simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]

/-- The scan after a `<` operator found no `>`. -/
theorem refuseTypeArgumentLookalike_inv {s s' : ParseState} {lt : Token}
    (h : Parse.refuseTypeArgumentLookalike lt s = .ok () s') :
    s' = s ∧ closesKinds 0 ((s.rest.drop 1).map (·.kind)) = false := by
  simp only [Parse.refuseTypeArgumentLookalike] at h
  rw [get_bind] at h
  by_cases hc : Parse.closesTypeArguments 0 (s.rest.drop 1) = true
  · rw [if_pos hc] at h; exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)
  · rw [if_neg hc] at h
    simp only [Parse.pure_ok] at h
    exact ⟨h.2.symm, by rw [← closesTypeArguments_kinds]; simpa using hc⟩

theorem requireFeature_inv {s s' : ParseState} {t : Token} {f : Feature}
    (h : Parse.requireFeature t f s = .ok () s') : s' = s ∧ s.target.supports f = true := by
  simp only [Parse.requireFeature] at h
  rw [get_bind] at h
  by_cases hc : s.target.supports f = true
  · simp only [hc, ↓reduceIte, Parse.pure_ok] at h
    exact ⟨h.2.symm, hc⟩
  · simp only [hc] at h; exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)

theorem peek_eq' (s : ParseState) : Parse.peek s = .ok (s.rest[0]?.getD s.eof) s := Parse.peekAt_rest s 0

theorem refuseArrowLookalike_inv {s s' : ParseState} (h : Parse.refuseArrowLookalike s = .ok () s') : s' = s := by
  simp only [Parse.refuseArrowLookalike] at h
  rw [Parse.bind_eq (peek_eq' s)] at h
  split at h
  · exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)
  · simp only [Parse.pure_ok] at h; exact h.2.symm

theorem refuseAsyncArrowLookalike_inv {s s' : ParseState} (h : Parse.refuseAsyncArrowLookalike s = .ok () s') :
    s' = s := by
  simp only [Parse.refuseAsyncArrowLookalike] at h
  rw [Parse.bind_ok] at h
  obtain ⟨_, s₁, h₁, h⟩ := h
  obtain rfl := refuseArrowLookalike_inv h₁
  rw [Parse.bind_eq (peek_eq' _)] at h
  split at h
  · exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)
  · simp only [Parse.pure_ok] at h; exact h.2.symm

/-- A check that refuses or does nothing leaves the state, when it does not refuse. -/
theorem check_inv {c : Prop} [Decidable c] {t : Token} {m : String} {s s' : ParseState}
    (h : (if c then Parse.failAt t m else pure PUnit.unit) s = .ok () s') : s' = s := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)
  · rw [if_neg hc] at h; simp only [Parse.pure_ok] at h; exact h.2.symm

theorem refuseSplitMember_inv {s s' : ParseState} (h : Parse.refuseSplitMember s = .ok () s') : s' = s := by
  simp only [Parse.refuseSplitMember] at h
  rw [Parse.bind_eq (peek_eq' s), Parse.bind_eq (Parse.peekAt_rest s 1)] at h
  exact check_inv h

/-- `readPropertyName` reads a name or a reserved word. -/
theorem readPropertyName_inv {s s' : ParseState} {n : String} (h : Ready s)
    (he : Parse.readPropertyName s = .ok n s') :
    ∃ t r, (t.kind = .ident n ∨ t.kind = .keyword n) ∧ s.rest = t :: r ∧ s' = past s t r ∧ Ready s' := by
  obtain ⟨x, r, hs⟩ := h.cons
  simp only [Parse.readPropertyName] at he
  rw [Parse.bind_ok] at he
  obtain ⟨t, s₁, ha, he⟩ := he
  obtain ⟨rfl, hpast⟩ := advance_inv h hs ha
  generalize hk : t.kind = k at he hpast
  cases k with
  | ident name =>
    obtain ⟨rfl, hR⟩ := hpast (by simp)
    simp only [Parse.pure_ok] at he; obtain ⟨rfl, rfl⟩ := he
    exact ⟨t, r, .inl hk, hs, rfl, hR⟩
  | keyword name =>
    obtain ⟨rfl, hR⟩ := hpast (by simp)
    simp only [Parse.pure_ok] at he; obtain ⟨rfl, rfl⟩ := he
    exact ⟨t, r, .inr hk, hs, rfl, hR⟩
  | _ => simp at he

/-! ### Lists -/

/-- Facts that a parser of list items gives for each item it reads. -/
def GivesItem {α : Type} (T : Edition) (wf : α → Bool) (tokens : α → List TokenKind)
    (afterOK : List TokenKind → α → Bool) (p : ParseM α) : Prop :=
  ∀ s x s', Ready s → s.target = T → p s = .ok x s' →
    Ready s' ∧ Kept s s' ∧ (∃ src, s.rest = src ++ s'.rest ∧ skel (src.map (·.kind)) = skel (tokens x)) ∧
      wf x = true ∧ ∀ after, Follows (s'.rest.map (·.kind)) after → afterOK after x = true

theorem joined_snoc (sep : String) : ∀ (xs : List (List TokenKind)) (y : List TokenKind), xs ≠ [] →
    joined sep (xs ++ [y]) = joined sep xs ++ .punct sep :: y
  | [x], y, _ => by simp [joined]
  | x :: x' :: xs, y, _ => by
    have := joined_snoc sep (x' :: xs) y (by simp)
    simp only [List.cons_append, joined] at this ⊢
    rw [this]; simp

theorem ListAfter.snoc {α : Type} {afterOK : List TokenKind → α → Bool} {tokens : α → List TokenKind}
    {C : List TokenKind} : ∀ (items : List α) (x : α),
      ListAfter afterOK tokens (.punct "," :: tokens x ++ C) items → afterOK C x = true →
      ListAfter afterOK tokens C (items ++ [x])
  | [], x, _, hx => by simpa [ListAfter] using hx
  | [a], x, ha, hx => by
    simp only [ListAfter] at ha
    simp only [List.cons_append, List.nil_append, ListAfter]
    exact ⟨by simpa [joined] using ha, hx⟩
  | a :: b :: rest, x, ha, hx => by
    simp only [ListAfter] at ha
    obtain ⟨ha1, ha2⟩ := ha
    have ih := ListAfter.snoc (b :: rest) x ha2 hx
    simp only [List.cons_append, ListAfter] at ih ⊢
    refine ⟨?_, ih⟩
    have hj := joined_snoc "," ((b :: rest).map tokens) (tokens x) (by simp)
    simp only [List.map_cons, List.cons_append] at hj
    simp only [List.map_cons, List.map_append, List.map_nil]
    rw [hj]
    simpa using ha1

theorem Expr.afterOKList_of {close : List TokenKind} :
    ∀ es : List Expr, ListAfter (fun after e => e.afterOK after) Expr.tokens close es →
      Expr.afterOKList close es = true
  | [], _ => by simp [Expr.afterOKList]
  | [e], h => by simpa [Expr.afterOKList, ListAfter] using h
  | e :: f :: rest, h => by
    simp only [ListAfter] at h
    simp only [Expr.afterOKList, Bool.and_eq_true]
    exact ⟨h.1, Expr.afterOKList_of (f :: rest) h.2⟩

theorem Property.afterOKList_of {close : List TokenKind} :
    ∀ ps : List Property, ListAfter (fun after q => q.afterOK after) Property.tokens close ps →
      Property.afterOKList close ps = true
  | [], _ => by simp [Property.afterOKList]
  | [q], h => by simpa [Property.afterOKList, ListAfter] using h
  | q :: f :: rest, h => by
    simp only [ListAfter] at h
    simp only [Property.afterOKList, Bool.and_eq_true]
    exact ⟨h.1, Property.afterOKList_of (f :: rest) h.2⟩

theorem skel_joined_snoc (xs : List (List TokenKind)) (y : List TokenKind) :
    skel (joined "," (xs ++ [y])) = skel (joined "," xs) ++ skel y := by
  cases xs with
  | nil => simp [joined, skel]
  | cons x xs =>
    rw [joined_snoc "," (x :: xs) y (by simp), skel_append]
    simp [skel, skelKind]

/-- The loop over a list, after the items `items`, at `st`, from `s₀`. -/
def ListSoFar {α : Type} (wf : α → Bool) (tokens : α → List TokenKind) (afterOK : List TokenKind → α → Bool)
    (s₀ : ParseState) (items : Array α) (st : ParseState) : Prop :=
  Ready st ∧ Kept s₀ st ∧
    (∃ src, s₀.rest = src ++ st.rest ∧ skel (src.map (·.kind)) = skel (joined "," (items.toList.map tokens))) ∧
    (∀ x ∈ items.toList, wf x = true) ∧
    ∀ C, Follows (st.rest.map (·.kind)) C → ListAfter afterOK tokens C items.toList

theorem listStep_inv {α : Type} {T : Edition} {wf : α → Bool} {tokens : α → List TokenKind}
    {afterOK : List TokenKind → α → Bool} {close : String} {refuse : Token → ParseM Unit} {p : ParseM α}
    (hp : GivesItem T wf tokens afterOK p) (hrefuse : ∀ t s s', refuse t s = .ok () s' → s' = s)
    {s₀ : ParseState} {items items' : Array α} {b : Bool} {st st' : ParseState} (hT : s₀.target = T)
    (hI : ListSoFar wf tokens afterOK s₀ items st) (h : Parse.listStep close refuse p items st = .ok (items', b) st') :
    ListSoFar wf tokens afterOK s₀ items' st' := by
  obtain ⟨hR, hK, ⟨src, hsrc, hskel⟩, hwf, hafter⟩ := hI
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.listStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : x.isPunct close = true
  · rw [if_pos hc] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR, hK, ⟨src, hsrc, hskel⟩, hwf, hafter⟩
  · rw [if_neg hc, Parse.pure_bind, Parse.bind_ok] at h
    obtain ⟨_, s₁, hr1, h⟩ := h
    obtain rfl := hrefuse _ _ _ hr1
    rw [Parse.bind_ok] at h
    obtain ⟨y, s₂, hy, h⟩ := h
    obtain ⟨hR₂, hK₂, ⟨ysrc, hysrc, hyskel⟩, hywf, hyafter⟩ := hp _ _ _ hR (hK.target_eq.trans hT) hy
    obtain ⟨z, r₂, hs₂⟩ := hR₂.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
    have hwf' : ∀ x ∈ (items.push y).toList, wf x = true := by
      intro x' hx'
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx'
      rcases hx' with hx' | rfl
      · exact hwf x' hx'
      · exact hywf
    -- What follows the item is what follows `st₃`, the state after any `,`.
    have hdone : ∀ (c : List Token) (st₃ : ParseState), s₂.rest = c ++ st₃.rest → skel (c.map (·.kind)) = [] →
        Ready st₃ → Kept s₂ st₃ → ListSoFar wf tokens afterOK s₀ (items.push y) st₃ := by
      intro c st₃ hc3 hcs hR₃ hK₃
      have hst : s₁.rest = ysrc ++ c ++ st₃.rest := by rw [hysrc, hc3, List.append_assoc]
      refine ⟨hR₃, hK.trans (hK₂.trans hK₃), ⟨src ++ ysrc ++ c, ?_, ?_⟩, hwf', fun C hC => ?_⟩
      · rw [hsrc, hst]; simp
      · rw [Array.toList_push]
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [skel_joined_snoc, ← hskel, ← hyskel]
        simp [skel_append, hcs]
      · have h2 : Follows (s₂.rest.map (·.kind)) C := by
          rw [hc3, List.map_append]
          exact hC.prefix (p' := []) (by simpa using hcs) (by simp)
        have h1 : Follows (s₁.rest.map (·.kind)) (.punct "," :: tokens y ++ C) := by
          rw [hysrc, List.map_append]
          exact h2.prefix (p' := .punct "," :: tokens y) (by rw [hyskel]; simp [skel, skelKind]) (by simp)
        rw [Array.toList_push]
        exact ListAfter.snoc _ y (hafter _ h1) (hyafter C h2)
    by_cases hz : z.isPunct "," = true
    · have hzk : z.kind = .punct "," := by simpa [Token.isPunct] using hz
      have hne : z.kind ≠ .eof := by rw [hzk]; simp
      rw [if_pos hz, Parse.bind_eq (Parse.discard_eq (advance_past hR₂ hs₂ hne))] at h
      simp only [Parse.pure_ok, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, _⟩, rfl⟩ := h
      exact hdone [z] _ (by simpa using hs₂) (by simp [hzk, skel, skelKind]) (hR₂.past hs₂ (hR₂.more hs₂ hne))
        (Kept.past _ _ _)
    · rw [if_neg hz] at h
      by_cases hz2 : (!z.isPunct close) = true
      · rw [if_pos hz2] at h; exact absurd h (unexpected_bind_ne_ok _ _ _ _ _ _)
      · rw [if_neg hz2, Parse.pure_bind] at h
        simp only [Parse.pure_ok, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, _⟩, rfl⟩ := h
        exact hdone [] s₂ (by simp) (by simp [skel]) hR₂ (Kept.refl _)

/-! ### Levels -/

theorem wfAt_lhs_of_primary {T : Edition} : ∀ {e : Expr}, e.wfAt T .primary = true → e.wfAt T .lhs = true := by
  intro e h; cases e <;> simp_all [Expr.wfAt]

theorem wfAt_postfix_of_lhs {T : Edition} : ∀ {e : Expr}, e.wfAt T .lhs = true → e.wfAt T .postfix = true := by
  intro e h; cases e <;> simp_all [Expr.wfAt]

theorem wfAt_unary_of_postfix {T : Edition} : ∀ {e : Expr}, e.wfAt T .postfix = true → e.wfAt T .unary = true := by
  intro e h; cases e <;> simp_all [Expr.wfAt]

theorem wfAt_bin_of_unary {T : Edition} {m : Nat} : ∀ {e : Expr}, e.wfAt T .unary = true → e.wfAt T (.bin m) = true := by
  intro e h; cases e <;> simp_all [Expr.wfAt]

/-- A binary node that `parseBinary` reads from precedence `m` it also reads
from any lower precedence. -/
theorem wfAt_bin_mono {T : Edition} {m m' : Nat} (hm : m' ≤ m) :
    ∀ {e : Expr}, e.wfAt T (.bin m) = true → e.wfAt T (.bin m') = true
  | .binary sp op l r, h => by
    simp only [Expr.wfAt, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    exact ⟨⟨⟨⟨⟨⟨by omega, h2⟩, wfAt_bin_mono hm h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  | .asConst sp e, h => by
    simp only [Expr.wfAt, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨by omega, wfAt_bin_mono hm h.1.2⟩, h.2⟩
  | .satisfies sp e t, h => by
    simp only [Expr.wfAt, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨⟨by omega, wfAt_bin_mono hm h.1.1.2⟩, h.1.2⟩, h.2⟩
  | .ident .., h | .number .., h | .bigint .., h | .string .., h | .bool .., h | .null _, h | .array .., h
  | .object .., h | .paren .., h | .member .., h | .optMember .., h | .index .., h | .call .., h
  | .unary .., h | .prefix .., h | .postfix .., h | .cond .., h | .assign .., h | .arrow .., h
  | .new .., h => by simp_all [Expr.wfAt]

theorem wfAt_cond_of_bin {T : Edition} {m : Nat} : ∀ {e : Expr}, e.wfAt T (.bin m) = true → e.wfAt T .cond = true := by
  intro e h
  have h0 := wfAt_bin_mono (Nat.zero_le m) h
  cases e <;> simp_all [Expr.wfAt]

theorem wfAt_assign_of_cond {T : Edition} : ∀ {e : Expr}, e.wfAt T .cond = true → e.wfAt T .assign = true := by
  intro e h; cases e <;> simp_all [Expr.wfAt]

/-! ### What the expression parser gives -/

theorem wordsOK_enclose {T : Edition} {o c : String} {items : List (List Word)}
    (ho : Lex.punctuators.contains o = true) (hc : Lex.punctuators.contains c = true)
    (h : ∀ x ∈ items, WordsOK T x) : WordsOK T (enclose o c items) := by
  simp only [enclose]
  exact WordsOK.cons (ok_punct ho) ((WordsOK.separated (sep := ",") (by decide) items h).append (WordsOK.word (ok_punct hc)))

theorem wordsOK_callBreak {T : Edition} (c : Expr) : WordsOK T (callBreak c) := by
  unfold callBreak; split
  · exact WordsOK.word (by simp [lineBreak, Word.ok])
  · exact WordsOK.nil

theorem Expr.wordsOK_of {T : Edition} {es : List Expr} (h : ∀ e ∈ es, WordsOK T e.words) :
    ∀ x ∈ Expr.wordsOf es, WordsOK T x := by
  intro x hx
  rw [Expr.wordsOf_eq] at hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact h e he

theorem Property.wordsOK_of {T : Edition} {ps : List Property} (h : ∀ q ∈ ps, WordsOK T q.words) :
    ∀ x ∈ Property.wordsOf ps, WordsOK T x := by
  intro x hx
  rw [Property.wordsOf_eq] at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  exact h q hq

/-- The word of a name or reserved word that the lexer gave, as a property name. -/
theorem propertyName_ok {T : Edition} {k : TokenKind} {n : String} (hk : k = .ident n ∨ k = .keyword n)
    (h : Word.ok T [k] = true) : Word.ok T (propertyName n) = true := by
  rcases hk with rfl | rfl
  · simp only [Word.ok, TokenKind.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
    have h2 : n ∉ Lex.reservedWords := by simpa using h.2
    simp [propertyName, h2, identWord, Word.ok, TokenKind.ok, h.1]
  · simp only [Word.ok, TokenKind.ok] at h
    have h2 : n ∈ Lex.reservedWords := by simpa using h
    simp [propertyName, h2, keywordWord, Word.ok, TokenKind.ok]

/-- What the parser gave when it read `e` from `s` to `s'` at `level`: the
state is still ready; the tokens it read have the skeleton and the first
token of `e`'s printed tokens; `e` is well formed at `level`; and the
parser's checks hold for every printed context that follows the source
context. -/
structure GaveE (T : Edition) (level : Level) (s : ParseState) (e : Expr) (s' : ParseState) : Prop where
  ready : Ready s'
  kept : Kept s s'
  tokens : ∃ src, s.rest = src ++ s'.rest ∧ skel (src.map (·.kind)) = skel e.tokens ∧
    (src.map (·.kind)).head? = e.tokens.head?
  wf : e.wfAt T level = true
  after : ∀ after, Follows (s'.rest.map (·.kind)) after → e.afterOK after = true
  ok : WordsOK T e.words

def GivesE (T : Edition) (level : Level) (p : ParseM Expr) : Prop :=
  ∀ s e s', Ready s → s.target = T → p s = .ok e s' → GaveE T level s e s'

theorem GaveE.lift {T : Edition} {l l' : Level} {s s' : ParseState} {e : Expr} (h : GaveE T l s e s')
    (hw : e.wfAt T l = true → e.wfAt T l' = true) : GaveE T l' s e s' :=
  ⟨h.ready, h.kept, h.tokens, hw h.wf, h.after, h.ok⟩

/-- The first token of `src ++ x`, when `src` has the first token of `ks`. -/
theorem head_append2 {src x : List Token} {ks y : List TokenKind} (hks : ks ≠ [])
    (h : (src.map (·.kind)).head? = ks.head?) : ((src ++ x).map (·.kind)).head? = (ks ++ y).head? := by
  cases ks with
  | nil => exact absurd rfl hks
  | cons k ks => cases src with
    | nil => simp at h
    | cons t src => simpa using h

theorem head_append_ne {a b : List TokenKind} {k : TokenKind} (ha : a.head? ≠ some k) (hne : a ≠ []) :
    (a ++ b).head? ≠ some k := by
  cases a with
  | nil => exact absurd rfl hne
  | cons x a => simpa using ha

theorem parseExpression_gives {T : Edition} {f : Nat} (hA : GivesE T .assign (Parse.parseAssign f)) :
    GivesE T .assign (Parse.parseExpression (f + 1)) := by
  intro s e s' hR hT h
  simp only [Parse.parseExpression] at h
  rw [Parse.bind_ok] at h
  obtain ⟨x, s₁, hx, h⟩ := h
  have hg := hA _ _ _ hR hT hx
  obtain ⟨y, r, hs⟩ := hg.ready.cons
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : y.isPunct "," = true
  · rw [if_pos hc] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)
  · rw [if_neg hc, Parse.pure_bind] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact hg

theorem symbol_assignOp_head (op : AssignOp) : (symbol op.symbol).head? ≠ some (.punct "{") := by
  cases op <;> simp (config := { decide := true }) [symbol, AssignOp.symbol, punctWord]

theorem symbol_binOp_head (op : BinOp) : (symbol op.symbol).head? ≠ some (.punct "{") := by
  cases op <;> simp (config := { decide := true }) [symbol, BinOp.symbol, punctWord,
    keywordWord]

/-- The rest of `parseAssign` after its operator: the value, and the node. -/
theorem assign_tail {T : Edition} {f : Nat} (hA : GivesE T .assign (Parse.parseAssign f))
    {s s₁ s' : ParseState} {lhs e : Expr} {op : AssignOp} {w : Nat} {start : Pos}
    (hT : s.target = T) (gl : GaveE T .cond s lhs s₁)
    (hop : ∃ a r, s₁.rest = a ++ r ∧ a.length = w ∧ a.map (·.kind) = symbol op.symbol ∧ r ≠ [])
    (hsimple : lhs.isSimpleTarget = true) (hallow : op.allowedIn T = true)
    (h : (Parse.skip w >>= fun _ => Parse.parseAssign f >>= fun value =>
      Parse.spanFrom start >>= fun sp => pure (Expr.assign sp op lhs value)) s₁ = .ok e s') :
    GaveE T .assign s e s' := by
  obtain ⟨a, r, ha, rfl, hk, hr⟩ := hop
  rw [Parse.bind_ok] at h
  obtain ⟨_, s₂, hsk, h⟩ := h
  obtain ⟨hs₂, hR₂, hK₂⟩ := skip_inv gl.ready ha hr hsk
  rw [Parse.bind_ok] at h
  obtain ⟨value, s₃, hv, h⟩ := h
  have gv := hA _ _ _ hR₂ (by rw [hK₂.target_eq, gl.kept.target_eq, hT]) hv
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨lsrc, hl1, hl2, hl3⟩ := gl.tokens
  obtain ⟨vsrc, hv1, hv2, _⟩ := gv.tokens
  have hst : s₁.rest = a ++ vsrc ++ s₃.rest := by rw [ha, ← hs₂, hv1, List.append_assoc]
  refine ⟨gv.ready, gl.kept.trans (hK₂.trans gv.kept), ⟨lsrc ++ a ++ vsrc, ?_, ?_, ?_⟩, ?_, ?_,
    by simpa [Expr.words] using gl.ok.append (WordsOK.cons (assignOp_ok T op) gv.ok)⟩
  · rw [hl1, hst]; simp
  · rw [Expr.tokens_assign, List.append_assoc]; simp only [List.map_append, skel_append, hl2, hk, hv2, List.append_assoc]
  · rw [Expr.tokens_assign, List.append_assoc, List.append_assoc]; exact head_append2 (Expr.tokens_ne_nil lhs) hl3
  · simp only [Expr.wfAt, Bool.and_eq_true]
    exact ⟨⟨⟨gl.wf, hsimple⟩, hallow⟩, gv.wf⟩
  · intro after hf
    simp only [Expr.afterOK, Bool.and_eq_true]
    refine ⟨gl.after _ ?_, gv.after _ hf⟩
    have := hf.prefix (p := (a ++ vsrc).map (·.kind)) (p' := symbol op.symbol ++ value.tokens)
      (by simp only [List.map_append, skel_append, hk, hv2])
      (head_append_ne (symbol_assignOp_head op) (List.ne_nil_of_length_pos (length_symbol_assignOp op)))
    simpa [hst, List.append_assoc] using this

theorem parseAssign_gives {T : Edition} {f : Nat} (hA : GivesE T .assign (Parse.parseAssign f))
    (hC : GivesE T .cond (Parse.parseConditional f)) (hW : GivesE T .assign (Parse.parseArrow f)) :
    GivesE T .assign (Parse.parseAssign (f + 1)) := by
  intro s e s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseAssign] at h
  rw [Parse.bind_eq (Parse.startsArrow_eq s)] at h
  cases harr : Parse.arrowStart (s.rest.map (·.kind)) with
  | true =>
    simp only [harr, ↓reduceIte] at h
    rw [Parse.bind_ok] at h
    obtain ⟨e', s₁, he, h⟩ := h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact hW _ _ _ hR hT he
  | false =>
  simp only [harr, Bool.false_eq_true, ↓reduceIte] at h
  rw [Parse.pure_bind] at h
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_ok] at h
  obtain ⟨lhs, s₁, hl, h⟩ := h
  have gl := hC _ _ _ hR hT hl
  obtain ⟨y, r₁, hs₁⟩ := gl.ready.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
  by_cases harrow : y.isPunct "=>" = true
  · rw [if_pos harrow] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)
  rw [if_neg harrow, Parse.pure_bind, Parse.bind_ok] at h
  obtain ⟨v, s₂, hv, h⟩ := h
  have hT₁ : s₁.target = T := gl.kept.target_eq.trans hT
  obtain ⟨rfl, hop⟩ := peekAssignOp_inv gl.ready hv
  cases v with
  | none =>
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact gl.lift wfAt_assign_of_cond
  | some pw =>
    obtain ⟨op, w⟩ := pw
    have hop' := hop op w rfl
    simp only at h
    by_cases hsimple : lhs.isSimpleTarget = true
    · rw [if_pos hsimple, Parse.pure_bind] at h
      cases op <;> simp only at h <;> first
        | (rw [Parse.bind_ok] at h
           obtain ⟨_, s₃, hf, h⟩ := h
           obtain ⟨rfl, hsup⟩ := requireFeature_inv hf
           exact assign_tail hA hT gl hop' hsimple (by simpa [AssignOp.allowedIn, hT₁] using hsup) h)
        | (rw [Parse.pure_bind] at h
           exact assign_tail hA hT gl hop' hsimple (by simp [AssignOp.allowedIn]) h)
    · rw [if_neg hsimple] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)

/-- No binary operator of precedence `m` or more comes next. -/
def StopsBin (m : Nat) (s : ParseState) : Prop :=
  (∀ v s', Parse.peekBinaryOp s = .ok v s' → ∀ op w, v = some (op, w) → op.precedence < m) ∧
    ∀ x r, s.rest = x :: r → Parse.isTypeOperator x = true → BinOp.lt.precedence < m

/-- When `e` ends in `as const` or `satisfies T`, the next token is none of
`Parse.typeEnders`, which the parser refuses there. -/
def TypeStop (e : Expr) (s : ParseState) : Prop :=
  e.endsInType = true → ∀ x r, s.rest = x :: r → ∀ p, x.kind = .punct p → p ∉ Parse.typeEnders

def GivesBin (T : Edition) (m : Nat) (p : ParseM Expr) : Prop :=
  ∀ s e s', Ready s → s.target = T → p s = .ok e s' → GaveE T (.bin m) s e s' ∧ StopsBin m s' ∧ TypeStop e s'

theorem skel_cons (k : TokenKind) (l : List TokenKind) :
    skel (k :: l) = if skelKind k then k :: skel l else skel l := by
  simp only [skel, List.filter_cons]

theorem parseConditional_gives {T : Edition} {f : Nat} (hA : GivesE T .assign (Parse.parseAssign f))
    (hB : GivesBin T 0 (Parse.parseBinary f 0)) : GivesE T .cond (Parse.parseConditional (f + 1)) := by
  intro s e s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseConditional] at h
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_ok] at h
  obtain ⟨test, s₁, ht, h⟩ := h
  have gt := (hB _ _ _ hR hT ht).1
  have hts := (hB _ _ _ hR hT ht).2.2
  obtain ⟨q, r₁, hs₁⟩ := gt.ready.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
  by_cases hq : q.isPunct "?" = true
  · rw [if_neg (by simp [hq]), Parse.pure_bind] at h
    have hqk : q.kind = .punct "?" := by simpa [Token.isPunct] using hq
    have hne : q.kind ≠ .eof := by rw [hqk]; simp
    have hR₂ := gt.ready.past hs₁ (gt.ready.more hs₁ hne)
    rw [Parse.bind_eq (Parse.discard_eq (advance_past gt.ready hs₁ hne)), Parse.bind_ok] at h
    obtain ⟨a, s₂, ha, h⟩ := h
    have ga := hA _ _ _ hR₂ (by rw [Kept.past _ _ _ |>.target_eq, gt.kept.target_eq, hT]) ha
    rw [Parse.bind_ok] at h
    obtain ⟨c, s₃, hc, h⟩ := h
    obtain ⟨hck, r₃, hs₃, rfl, hR₃⟩ := expectPunct_inv ga.ready hc
    rw [Parse.bind_ok] at h
    obtain ⟨b, s₄, hb, h⟩ := h
    have gb := hA _ _ _ hR₃ (by
      rw [show (past s₂ c r₃).target = s₂.target from rfl, ga.kept.target_eq, (Kept.past _ _ _).target_eq,
        gt.kept.target_eq, hT]) hb
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨tsrc, ht1, ht2, ht3⟩ := gt.tokens
    obtain ⟨asrc, ha1, ha2, _⟩ := ga.tokens
    obtain ⟨bsrc, hb1, hb2, _⟩ := gb.tokens
    have hr₁ : r₁ = asrc ++ c :: bsrc ++ s₄.rest := by
      have h1 : (past (past s q r₁) q r₁).rest = r₁ := rfl
      simp only at ha1 hb1
      rw [ha1, hs₃, hb1]; simp
    refine ⟨gb.ready, gt.kept.trans ((Kept.past _ _ _).trans (ga.kept.trans ((Kept.past _ _ _).trans gb.kept))),
      ⟨tsrc ++ q :: asrc ++ c :: bsrc, ?_, ?_, ?_⟩, ?_, ?_,
      by simpa [Expr.words, punctWord, List.append_assoc] using gt.ok.append (WordsOK.cons (ok_punct (p := "?") (by decide))
        (ga.ok.append (WordsOK.cons (ok_punct (p := ":") (by decide)) gb.ok)))⟩
    · rw [ht1, hs₁, hr₁]; simp
    · rw [Expr.tokens_cond, List.append_assoc]
      simp (config := { decide := true }) only [List.map_append, List.map_cons, skel_append, skel_cons, ht2,
        ha2, hb2, hqk, hck, ↓reduceIte, List.append_assoc]
    · rw [Expr.tokens_cond, List.append_assoc, List.append_assoc]; exact head_append2 (Expr.tokens_ne_nil test) ht3
    · simp only [Expr.wfAt, Bool.and_eq_true]
      refine ⟨⟨⟨gt.wf, ga.wf⟩, gb.wf⟩, ?_⟩
      cases hte : test.endsInType
      · rfl
      · exact absurd (by decide : "?" ∈ Parse.typeEnders) (hts hte q r₁ hs₁ "?" hqk)
    · intro after hf
      simp only [Expr.afterOK, Bool.and_eq_true]
      have hfb := hf
      have hfa : Follows ((c :: bsrc ++ s₄.rest).map (·.kind)) (.punct ":" :: b.tokens ++ after) := by
        have := hf.prefix (p := (c :: bsrc).map (·.kind)) (p' := .punct ":" :: b.tokens)
          (by simp (config := { decide := true }) only [List.map_cons, skel_cons, hck, hb2, ↓reduceIte]) (by simp)
        simpa [List.append_assoc] using this
      have hft : Follows ((q :: (asrc ++ c :: bsrc ++ s₄.rest)).map (·.kind))
          (.punct "?" :: a.tokens ++ .punct ":" :: b.tokens ++ after) := by
        have := hfa.prefix (p := (q :: asrc).map (·.kind)) (p' := .punct "?" :: a.tokens)
          (by simp (config := { decide := true }) only [List.map_cons, skel_cons, hqk, ha2, ↓reduceIte]) (by simp)
        simpa [List.append_assoc] using this
      refine ⟨⟨gt.after _ ?_, ga.after _ ?_⟩, gb.after _ hfb⟩
      · rw [hs₁, hr₁]; simpa [List.append_assoc] using hft
      · rw [hs₃, show r₃ = bsrc ++ s₄.rest from hb1]; simpa [List.append_assoc] using hfa
  · rw [if_pos (by simp [hq])] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact gt.lift wfAt_cond_of_bin

/-- An `if` without `else` in a do-block, which the compiler writes with the
rest of the block in both branches: the rest runs after the action, or after
nothing. -/
theorem seq_inv {β : Type} {c : Prop} [Decidable c] {a : ParseM PUnit} {K : PUnit → ParseM β}
    {s s' : ParseState} {r : β} (h : (if c then a >>= K else pure PUnit.unit >>= K) s = .ok r s') :
    ∃ s₁, (c → a s = .ok () s₁) ∧ (¬c → s₁ = s) ∧ K () s₁ = .ok r s' := by
  by_cases hc : c
  · rw [if_pos hc, Parse.bind_ok] at h
    obtain ⟨u, s₁, ha, hK⟩ := h
    exact ⟨s₁, fun _ => ha, fun hn => absurd hc hn, hK⟩
  · rw [if_neg hc, Parse.pure_bind] at h
    exact ⟨s, fun hc' => absurd hc' hc, fun _ => rfl, h⟩

/-- An `if` without `else` that refuses: the parser went on, so the condition
does not hold. -/
theorem fail_inv {β : Type} {c : Prop} [Decidable c] {t : Token} {msg : String} {K : PUnit → ParseM β}
    {s s' : ParseState} {r : β} (h : (if c then Parse.failAt t msg >>= K else pure PUnit.unit >>= K) s = .ok r s') :
    ¬c ∧ K () s = .ok r s' := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)
  · rw [if_neg hc, Parse.pure_bind] at h; exact ⟨hc, h⟩

/-- The left operand of a binary node binds at least as tightly as the node:
the parser read the operator where the operand's own right operand stopped. -/
def LeftStop (acc : Expr) (st : ParseState) : Prop :=
  ∀ sp op' l r, acc = .binary sp op' l r → StopsBin (rhsPrec op') st

theorem BinOp.precedence_le (op : BinOp) : op.precedence ≤ 12 := by cases op <;> decide

theorem BinOp.precedence_twelve {op : BinOp} (h : op.precedence = 12) : op = .exp := by
  cases op <;> simp_all [BinOp.precedence]

/-- The operator after a binary node's right operand binds no tighter than the node. -/
theorem leftOK_of {op : BinOp} {acc : Expr} {st : ParseState} {w : Nat}
    (hls : LeftStop acc st) (hv : Parse.peekBinaryOp st = .ok (some (op, w)) st)
    (hexp : op = .exp → ∀ sp uop arg, acc ≠ .unary sp uop arg) :
    leftOK op acc = true := by
  cases acc with
  | binary sp' op' l' r' =>
    have h1 := (hls sp' op' l' r' rfl).1 _ _ hv op w rfl
    have hle := BinOp.precedence_le op'
    have hle' := BinOp.precedence_le op
    simp only [leftOK, bne, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    by_cases he' : op' = .exp
    · subst he'
      simp only [rhsPrec, beq_self_eq_true, ↓reduceIte] at h1
      refine ⟨?_, Nat.le_of_lt h1⟩
      cases he : op == BinOp.exp
      · rfl
      · rw [beq_iff_eq] at he; subst he; exact absurd h1 (Nat.lt_irrefl _)
    · have h2 : rhsPrec op' = op'.precedence + 1 := by simp [rhsPrec, he']
      rw [h2] at h1
      have hne : op'.precedence ≠ 12 := fun h => he' (BinOp.precedence_twelve h)
      refine ⟨?_, by omega⟩
      cases op <;> simp_all [BinOp.precedence] <;> omega
  | unary sp' uop arg =>
    simp only [leftOK, bne, Bool.not_eq_true']
    cases he : op == BinOp.exp
    · rfl
    · rw [beq_iff_eq] at he; exact absurd rfl (hexp he sp' uop arg)
  | _ => simp [leftOK]

/-- What the `??` checks of `binaryStep` give, as `wfAt` states them. -/
theorem mixing_of {op : BinOp} {l r : Expr}
    (h : ¬(op == BinOp.coalesce && (l.isLogical || r.isLogical) ||
      (op == BinOp.and || op == BinOp.or) && (l.isCoalesce || r.isCoalesce)) = true) :
    (if op == .coalesce then !l.isLogical && !r.isLogical
      else if op == .and || op == .or then !l.isCoalesce && !r.isCoalesce else true) = true := by
  by_cases h1 : op = .coalesce
  · subst h1; simp_all
  · by_cases h2 : op = .and
    · subst h2; simp_all
    · by_cases h3 : op = .or
      · subst h3; simp_all
      · simp_all

/-- A token of a binary operator is not `as` or `satisfies`. -/
theorem isTypeOperator_binOp {op : BinOp} {a r r' : List Token} {x : Token} {rest : List Token}
    (hs : rest = a ++ r) (ha : a.map (·.kind) = symbol op.symbol) (hx : rest = x :: r') :
    Parse.isTypeOperator x = false := by
  obtain ⟨k, ks, hk, _⟩ := binOp_head op
  have hni := binOp_notIdent op hk
  rw [hk] at ha
  obtain ⟨y, a', rfl, hy, _⟩ := List.map_eq_cons_iff.mp ha
  rw [hs] at hx
  simp only [List.cons_append, List.cons.injEq] at hx
  obtain ⟨rfl, -⟩ := hx
  cases hxk : y.kind <;> simp_all [Parse.isTypeOperator, Token.isIdent]

/-- An operator after an operand that ends in a type is one that may follow it. -/
theorem followsType_of_op {op : BinOp} {a r : List Token} {e : Expr} {st : ParseState}
    (hts : TypeStop e st) (hs : st.rest = a ++ r) (ha : a.map (·.kind) = symbol op.symbol) :
    (!e.endsInType || op.followsType) = true := by
  cases hte : e.endsInType
  · rfl
  · have h := hts hte
    cases a with
    | nil => cases op <;> simp [BinOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord] at ha
    | cons x a' =>
      have hx := h x (a' ++ r) (by simpa using hs)
      simp only [List.map_cons] at ha
      cases op <;> simp [BinOp.followsType] <;>
        simp [BinOp.symbol, symbol, Lex.reservedWords, punctWord] at ha <;>
        first
          | exact absurd (by decide) (hx _ ha.1)
          | exact absurd (by decide) (hx _ ha)

/-- `refuseAfterType` passes only when the next token is none of `typeEnders`. -/
theorem refuseAfterType_inv {s s' : ParseState} {w : String} (hR : Ready s)
    (h : Parse.refuseAfterType w s = .ok () s') :
    s' = s ∧ ∀ x r, s.rest = x :: r → ∀ p, x.kind = .punct p → p ∉ Parse.typeEnders := by
  obtain ⟨y, r, hs⟩ := hR.cons
  simp only [Parse.refuseAfterType] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : Parse.typeEnders.any y.isPunct = true
  · rw [if_pos hc] at h; exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)
  · rw [if_neg hc] at h
    simp only [Parse.pure_ok] at h
    refine ⟨h.2.symm, fun x r' hx p hp hmem => hc ?_⟩
    rw [hs] at hx
    simp only [List.cons.injEq] at hx
    obtain ⟨rfl, -⟩ := hx
    exact List.any_eq_true.mpr ⟨p, hmem, by simp [Token.isPunct, hp]⟩

/-- The step of `parseBinary` where no binary operator comes: `as const` or
`satisfies T`, or the end of the loop. -/
theorem typeOperatorStep_inv {T : Edition} {m B : Nat} {start : Pos} {s₀ st st' : ParseState}
    {acc acc' : Expr} {b : Bool} (hT : s₀.target = T) (g : GaveE T (.bin m) s₀ acc st) (hls : LeftStop acc st)
    (hts : TypeStop acc st) (hv : Parse.peekBinaryOp st = .ok none st)
    (h : Parse.typeOperatorStep (Parse.parseType B) start m acc st = .ok (acc', b) st') :
    (GaveE T (.bin m) s₀ acc' st' ∧ LeftStop acc' st' ∧ TypeStop acc' st') ∧ (b = false → StopsBin m st') := by
  have hR := g.ready
  have hTs : st.target = T := g.kept.target_eq.trans hT
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.typeOperatorStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : (!Parse.isTypeOperator x || decide (BinOp.lt.precedence < m)) = true
  · rw [if_pos hc] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨⟨g, hls, hts⟩, fun _ => ⟨fun v' s' hv' op w he => ?_, fun y r' hy ht => ?_⟩⟩
    · obtain ⟨rfl, _⟩ := ok_unique hv hv'; simp at he
    · rw [hs] at hy
      simp only [List.cons.injEq] at hy
      obtain ⟨rfl, -⟩ := hy
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      rcases hc with h1 | h1
      · rw [h1] at ht; cases ht
      · exact h1
  · rw [if_neg hc, Parse.pure_bind] at h
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, Bool.not_eq_false] at hc
    obtain ⟨hxt, hm⟩ := hc
    obtain ⟨hrf, h⟩ := fail_inv h
    have hxk : x.kind = .ident "as" ∨ x.kind = .ident "satisfies" := by
      simp [Parse.isTypeOperator, Token.isIdent] at hxt
      exact hxt.1
    have hne : x.kind ≠ .eof := by rcases hxk with h' | h' <;> rw [h'] <;> simp
    have hxn : ∀ q, x.kind ≠ .punct q := by rcases hxk with h' | h' <;> rw [h'] <;> simp
    rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne))] at h
    have hR₁ := hR.past hs (hR.more hs hne)
    have hxok : Word.ok T [x.kind] = true := hTs ▸ hR.tok (by simp [hs]) hne
    obtain ⟨src, hg1, hg2, hg3⟩ := g.tokens
    have hleft : leftOKType acc = true := by
      cases acc with
      | binary sp' op' l' r' =>
        have h1 := (hls sp' op' l' r' rfl).2 x r hs hxt
        have hle := BinOp.precedence_le op'
        simp only [leftOKType, decide_eq_true_eq]
        unfold rhsPrec at h1
        split at h1 <;> simp_all [BinOp.precedence] <;> omega
      | _ => simpa [leftOKType] using hrf
    by_cases has : x.isIdent "as" = true
    · have hxa : x.kind = .ident "as" := by simpa [Token.isIdent] using has
      rw [if_pos has] at h
      obtain ⟨c, r₂, hs₁⟩ := hR₁.cons
      rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
      have hc : c.isKeyword "const" = true := by
        cases hcc : c.isKeyword "const"
        · rw [if_neg (by simp [hcc])] at h
          exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)
        · rfl
      have hck : c.kind = .keyword "const" := by simpa [Token.isKeyword] using hc
      have hcne : c.kind ≠ .eof := by rw [hck]; simp
      rw [if_pos hc, Parse.pure_bind] at h
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hs₁ hcne))] at h
      have hR₂ := hR₁.past hs₁ (hR₁.more hs₁ hcne)
      have hcok : Word.ok T [c.kind] = true := hTs ▸ hR₁.tok (by rw [hs₁]; simp) hcne
      rw [Parse.bind_ok] at h
      obtain ⟨_, s₃, hra, h⟩ := h
      obtain ⟨rfl, hok⟩ := refuseAfterType_inv hR₂ hra
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      have hr : r = c :: r₂ := hs₁
      refine ⟨⟨⟨hR₂, g.kept.trans ((Kept.past _ _ _).trans (Kept.past _ _ _)), ⟨src ++ [x, c], ?_, ?_, ?_⟩,
        ?_, ?_, ?_⟩, fun _ _ _ _ he => by simp at he, fun _ => hok⟩, fun hb => by simp at hb⟩
      · show s₀.rest = (src ++ [x, c]) ++ r₂
        rw [hg1, hs, hr]; simp
      · rw [Expr.tokens_asConst]
        rw [List.map_append, skel_append, skel_append, hg2]
        simp [hxa, hck, skel, skelKind]
      · rw [Expr.tokens_asConst]; exact head_append2 (Expr.tokens_ne_nil acc) hg3
      · simp only [Expr.wfAt, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨Nat.le_of_not_lt hm, g.wf⟩, hleft⟩
      · intro after hf
        simp only [Expr.afterOK]
        apply g.after
        have := hf.prefix (p := [x.kind, c.kind]) (p' := [.ident "as", .keyword "const"])
          (by simp [hxa, hck, skel, skelKind]) (by simp)
        rw [hs, hr]; simpa using this
      · simp only [Expr.words]
        exact g.ok.append (WordsOK.cons (by simpa [identWord, hxa] using hxok)
          (WordsOK.word (by simpa [keywordWord, hck] using hcok)))
    · have hxs : x.kind = .ident "satisfies" := by
        rcases hxk with h' | h'
        · simp [Token.isIdent, h'] at has
        · exact h'
      rw [if_neg has, Parse.pure_bind, Parse.bind_ok] at h
      obtain ⟨ty, s₂, hty, h⟩ := h
      obtain ⟨htw, hR₂, hK₂⟩ := (types_give T B).1 _ _ _ hR₁ (by rw [(Kept.past _ _ _).target_eq, hTs]) hty
      obtain ⟨-, tsrc, ht1, ht2⟩ := (types_skel B).1 _ _ _ hR₁ hty
      rw [Parse.bind_ok] at h
      obtain ⟨_, s₃, hra, h⟩ := h
      obtain ⟨rfl, hok⟩ := refuseAfterType_inv hR₂ hra
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      have hr : r = tsrc ++ s₃.rest := ht1
      refine ⟨⟨⟨hR₂, g.kept.trans ((Kept.past _ _ _).trans hK₂), ⟨src ++ x :: tsrc, ?_, ?_, ?_⟩,
        ?_, ?_, ?_⟩, fun _ _ _ _ he => by simp at he, fun _ => hok⟩, fun hb => by simp at hb⟩
      · rw [hg1, hs, hr]; simp
      · rw [Expr.tokens_satisfies]
        rw [List.map_append, skel_append, skel_append, hg2, List.map_cons, skel_cons, ht2]
        simp [hxs, skel_cons, skelKind]
      · rw [Expr.tokens_satisfies]; exact head_append2 (Expr.tokens_ne_nil acc) hg3
      · simp only [Expr.wfAt, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨Nat.le_of_not_lt hm, g.wf⟩, hleft⟩, both_left htw⟩
      · intro after hf
        simp only [Expr.afterOK]
        apply g.after
        have := hf.prefix (p := (x :: tsrc).map (·.kind)) (p' := .ident "satisfies" :: ty.tokens)
          (by simp [hxs, skel_cons, skelKind, ht2]) (by simp)
        rw [hs, hr]; simpa using this
      · simp only [Expr.words]
        exact g.ok.append (WordsOK.cons (by simpa [identWord, hxs] using hxok) (both_right htw))

theorem binaryStep_inv {T : Edition} {f m B : Nat} {start : Pos}
    (hB : ∀ m', GivesBin T m' (Parse.parseBinary f m'))
    {s₀ : ParseState} {acc acc' : Expr} {b : Bool} {st st' : ParseState} (hT : s₀.target = T)
    (hI : GaveE T (.bin m) s₀ acc st ∧ LeftStop acc st ∧ TypeStop acc st)
    (h : Parse.binaryStep (Parse.parseBinary f) (Parse.parseType B) start m acc st = .ok (acc', b) st') :
    (GaveE T (.bin m) s₀ acc' st' ∧ LeftStop acc' st' ∧ TypeStop acc' st') ∧ (b = false → StopsBin m st') := by
  obtain ⟨g, hls, hts⟩ := hI
  have hR := g.ready
  have hTs : st.target = T := g.kept.target_eq.trans hT
  simp only [Parse.binaryStep] at h
  rw [Parse.bind_ok] at h
  obtain ⟨v, s₁, hv, h⟩ := h
  obtain ⟨rfl, hop⟩ := peekBinaryOp_inv hR hv
  cases v with
  | none => exact typeOperatorStep_inv hT g hls hts hv h
  | some pw =>
    obtain ⟨op, w⟩ := pw
    simp only at h
    by_cases hp : op.precedence < m
    · rw [if_pos hp] at h
      simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      obtain ⟨a, r, ha, -, hk, -⟩ := hop op w rfl
      refine ⟨⟨g, hls, hts⟩, fun _ => ⟨fun v' s' hv' op' w' he => ?_, fun x r' hx ht => ?_⟩⟩
      · obtain ⟨rfl, _⟩ := ok_unique hv hv'
        simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact hp
      · rw [isTypeOperator_binOp ha hk hx] at ht; cases ht
    rw [if_neg hp, Parse.pure_bind] at h
    obtain ⟨a, r, ha, rfl, hk, hr⟩ := hop op w rfl
    obtain ⟨x, r', hs⟩ := hR.cons
    rw [Parse.bind_eq (Parse.peek_eq hs)] at h
    obtain ⟨hexp, h⟩ := fail_inv h
    have hleft := leftOK_of hls hv (fun he sp uop arg hacc => by subst hacc; simp [he] at hexp)
    obtain ⟨s₂, hlt1, hlt2, h⟩ := seq_inv h
    have e2 : s₂ = s₁ := by
      by_cases c : (op == BinOp.lt || op == BinOp.shl) = true
      · exact (refuseTypeArgumentLookalike_inv (hlt1 c)).1
      · exact hlt2 c
    obtain ⟨s₃, hx1, hx2, h⟩ := seq_inv h
    have e3 : s₃ = s₂ := by
      by_cases c : (op == BinOp.exp) = true
      · exact (requireFeature_inv (hx1 c)).1
      · exact hx2 c
    obtain ⟨s₄, hc1, hc2, h⟩ := seq_inv h
    have e4 : s₄ = s₃ := by
      by_cases c : (op == BinOp.coalesce) = true
      · exact (requireFeature_inv (hc1 c)).1
      · exact hc2 c
    have hT₂ : s₂.target = T := e2 ▸ hTs
    have hT₃ : s₃.target = T := e3 ▸ hT₂
    have hallow : op.allowedIn T = true := by
      simp only [BinOp.allowedIn, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
      refine ⟨?_, ?_⟩
      · by_cases c : op = .exp
        · subst c; exact .inr (hT₂ ▸ (requireFeature_inv (hx1 (by simp))).2)
        · exact .inl c
      · by_cases c : op = .coalesce
        · subst c; exact .inr (hT₃ ▸ (requireFeature_inv (hc1 (by simp))).2)
        · exact .inl c
    have hlt : (op == BinOp.lt || op == BinOp.shl) = true →
        closesKinds 0 ((s₁.rest.drop 1).map (·.kind)) = false := fun c => by
      exact (refuseTypeArgumentLookalike_inv (hlt1 c)).2
    rw [e4, e3, e2] at h
    rw [Parse.bind_ok] at h
    obtain ⟨_, s₅, hsk, h⟩ := h
    obtain ⟨hs₅, hR₅, hK₅⟩ := skip_inv hR ha hr hsk
    rw [Parse.bind_ok] at h
    obtain ⟨rhs, s₆, hrhs, h⟩ := h
    obtain ⟨gr, hstop, -⟩ := hB _ _ _ _ hR₅ (hK₅.target_eq.trans hTs) hrhs
    obtain ⟨hmix, h⟩ := fail_inv h
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨src, hg1, hg2, hg3⟩ := g.tokens
    obtain ⟨rsrc, hr1, hr2, _⟩ := gr.tokens
    have hst : s₁.rest = a ++ rsrc ++ s₆.rest := by rw [ha, ← hs₅, hr1, List.append_assoc]
    have hrp : (if (op == BinOp.exp) = true then op.precedence else op.precedence + 1) = rhsPrec op := rfl
    rw [hrp] at gr hstop
    refine ⟨⟨⟨gr.ready, g.kept.trans (hK₅.trans gr.kept), ⟨src ++ a ++ rsrc, ?_, ?_, ?_⟩, ?_, ?_,
      by simpa [Expr.words] using g.ok.append (WordsOK.cons (binOp_ok T op) gr.ok)⟩, ?_,
      fun hte => (hB _ _ _ _ hR₅ (hK₅.target_eq.trans hTs) hrhs).2.2 (by simpa [Expr.endsInType] using hte)⟩,
      fun hb => by simp at hb⟩
    · rw [hg1, hst]; simp
    · rw [Expr.tokens_binary, List.append_assoc]; simp only [List.map_append, skel_append, hg2, hk, hr2, List.append_assoc]
    · rw [Expr.tokens_binary, List.append_assoc, List.append_assoc]; exact head_append2 (Expr.tokens_ne_nil acc) hg3
    · simp only [Expr.wfAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨Nat.le_of_not_lt hp, hallow⟩, g.wf⟩, gr.wf⟩, hleft⟩, mixing_of hmix⟩,
        followsType_of_op hts ha hk⟩
    · intro after hf
      simp only [Expr.afterOK, Bool.and_eq_true]
      refine ⟨⟨?_, g.after _ ?_⟩, gr.after _ hf⟩
      · split
        · rename_i c
          have hsc := hlt c
          have hlen : a.length = 1 := by
            have := congrArg List.length hk
            rw [List.length_map] at this
            rw [this]
            simp only [Bool.or_eq_true, beq_iff_eq] at c
            rcases c with rfl | rfl <;> simp (config := { decide := true }) [symbol, BinOp.symbol, punctWord]
          have hdrop : s₁.rest.drop 1 = rsrc ++ s₆.rest := by
            rw [hst, List.append_assoc, ← hlen, List.drop_left]
          rw [hdrop, List.map_append] at hsc
          have h3 : closesKinds 0 (rhs.tokens ++ s₆.rest.map (·.kind)) = false := by
            rw [← hsc]; apply closesKinds_of_skel; simp [skel_append, hr2]
          simp [hf.1 _ h3]
        · rfl
      · have := hf.prefix (p := (a ++ rsrc).map (·.kind)) (p' := symbol op.symbol ++ rhs.tokens)
          (by simp only [List.map_append, skel_append, hk, hr2])
          (head_append_ne (symbol_binOp_head op) (List.ne_nil_of_length_pos (length_symbol_binOp op)))
        simpa [hst, List.append_assoc] using this
    · intro sp' op' l' r' he
      simp only [Expr.binary.injEq] at he
      obtain ⟨_, rfl, _, _⟩ := he
      exact hstop

theorem parseBinary_gives {T : Edition} {f m : Nat} (hB : ∀ m', GivesBin T m' (Parse.parseBinary f m'))
    (hU : GivesE T .unary (Parse.parseUnary f)) : GivesBin T m (Parse.parseBinary (f + 1) m) := by
  intro s e s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseBinary] at h
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
  obtain ⟨u, s₁, hu, h⟩ := h
  rw [Parse.bind_eq (Parse.budget_eq _)] at h
  have gu := hU _ _ _ hR hT hu
  have hI0 : GaveE T (.bin m) s u s₁ ∧ LeftStop u s₁ ∧ TypeStop u s₁ :=
    ⟨gu.lift wfAt_bin_of_unary, fun sp op l r he => by have := gu.wf; subst he; simp [Expr.wfAt] at this,
      fun he => by have := gu.wf; cases u <;> simp_all [Expr.wfAt, Expr.endsInType]⟩
  obtain ⟨hI, a₁, s₂, hI₁, hlast⟩ := iterate_inv
    (I := fun a st => GaveE T (.bin m) s a st ∧ LeftStop a st ∧ TypeStop a st)
    (fun a st a' b st' hI hst => (binaryStep_inv hB hT hI hst).1) _ u s₁ e s' hI0 h
  exact ⟨hI.1, (binaryStep_inv hB hT hI₁ hlast).2 rfl, hI.2.2⟩

theorem parseUnary_gives {T : Edition} {f : Nat} (hU : GivesE T .unary (Parse.parseUnary f))
    (hL : GivesE T .lhs (Parse.parseLeftHandSide f)) (hP : GivesE T .postfix (Parse.parsePostfix f)) :
    GivesE T .unary (Parse.parseUnary (f + 1)) := by
  intro s e s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseUnary] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  cases hu : Parse.unaryOp? x with
  | some op =>
    simp only [hu] at h
    have hk := unaryOp_inv hu
    have hne : x.kind ≠ .eof := by
      intro he; rw [he] at hk
      cases op <;> simp (config := { decide := true }) [symbol, UnaryOp.symbol, punctWord,
        keywordWord] at hk
    have hR₁ := hR.past hs (hR.more hs hne)
    rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)), Parse.bind_ok] at h
    obtain ⟨arg, s₂, ha, h⟩ := h
    have ga := hU _ _ _ hR₁ hT ha
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨asrc, ha1, ha2, _⟩ := ga.tokens
    refine ⟨ga.ready, (Kept.past _ _ _).trans ga.kept, ⟨x :: asrc, ?_, ?_, ?_⟩, ?_, ?_,
      by simpa [Expr.words, ← hk] using WordsOK.cons (hT ▸ hR.tok (by simp [hs]) hne) ga.ok⟩
    · rw [hs]; exact congrArg (x :: ·) ha1
    · rw [Expr.tokens_unary, ← hk]; simp only [List.map_cons, List.singleton_append, skel_cons, ha2]
    · rw [Expr.tokens_unary, ← hk]; simp
    · simpa [Expr.wfAt] using ga.wf
    · intro after hf; simpa [Expr.afterOK] using ga.after after hf
  | none =>
    simp only [hu] at h
    cases hp : Parse.updateOp? x with
    | some op =>
      simp only [hp] at h
      have hk := updateOp_inv hp
      have hne : x.kind ≠ .eof := by rw [hk]; simp
      have hR₁ := hR.past hs (hR.more hs hne)
      rw [Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)), Parse.bind_ok] at h
      obtain ⟨arg, s₂, ha, h⟩ := h
      have ga := hL _ _ _ hR₁ hT ha
      by_cases hsimple : arg.isSimpleTarget = true
      · rw [if_pos hsimple, Parse.pure_bind, Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨asrc, ha1, ha2, _⟩ := ga.tokens
        refine ⟨ga.ready, (Kept.past _ _ _).trans ga.kept, ⟨x :: asrc, ?_, ?_, ?_⟩, ?_, ?_,
          by simpa [Expr.words, punctWord, ← hk] using WordsOK.cons (hT ▸ hR.tok (by simp [hs]) hne) ga.ok⟩
        · rw [hs]; exact congrArg (x :: ·) ha1
        · rw [Expr.tokens_prefix]; simp only [List.map_cons, skel_cons, ha2, hk]
        · rw [Expr.tokens_prefix]; simp [hk]
        · simp only [Expr.wfAt, Bool.and_eq_true]; exact ⟨ga.wf, hsimple⟩
        · intro after hf; simpa [Expr.afterOK] using ga.after after hf
      · rw [if_neg hsimple] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)
    | none =>
      simp only [hp] at h
      exact (hP _ _ _ hR hT h).lift wfAt_unary_of_postfix

theorem parsePostfix_gives {T : Edition} {f : Nat} (hL : GivesE T .lhs (Parse.parseLeftHandSide f)) :
    GivesE T .postfix (Parse.parsePostfix (f + 1)) := by
  intro s e s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parsePostfix] at h
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_ok] at h
  obtain ⟨arg, s₁, ha, h⟩ := h
  have ga := hL _ _ _ hR hT ha
  obtain ⟨y, r₁, hs₁⟩ := ga.ready.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
  cases hp : Parse.updateOp? y with
  | none =>
    simp only [hp, Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ga.lift wfAt_postfix_of_lhs
  | some op =>
    simp only [hp] at h
    by_cases hnl : y.newlineBefore = true
    · rw [if_pos hnl] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      exact ga.lift wfAt_postfix_of_lhs
    rw [if_neg hnl, Parse.pure_bind] at h
    have hk := updateOp_inv hp
    have hne : y.kind ≠ .eof := by rw [hk]; simp
    by_cases hsimple : arg.isSimpleTarget = true
    · rw [if_pos hsimple, Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (advance_past ga.ready hs₁ hne)),
        Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨asrc, ha1, ha2, ha3⟩ := ga.tokens
      refine ⟨ga.ready.past hs₁ (ga.ready.more hs₁ hne), ga.kept.trans (Kept.past _ _ _),
        ⟨asrc ++ [y], ?_, ?_, ?_⟩, ?_, ?_, by
          simpa [Expr.words, punctWord, ← hk] using
            ga.ok.append (WordsOK.word ((ga.kept.target_eq.trans hT) ▸ ga.ready.tok (by simp [hs₁]) hne))⟩
      · rw [ha1, hs₁]; simp
      · rw [Expr.tokens_postfix]; simp only [List.map_append, List.map_cons, List.map_nil, skel_append, ha2, hk]
      · rw [Expr.tokens_postfix]; exact head_append2 (Expr.tokens_ne_nil arg) ha3
      · simp only [Expr.wfAt, Bool.and_eq_true]; exact ⟨ga.wf, hsimple⟩
      · intro after hf
        simp only [Expr.afterOK]
        apply ga.after
        have := hf.prefix (p := [y.kind]) (p' := [.punct op.symbol]) (by rw [hk])
          (by cases op <;> simp [UpdateOp.symbol])
        simpa [hs₁] using this
    · rw [if_neg hsimple] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)

/-! ### Lists of expressions and properties -/

/-- The loop over a list gives a list whose items are well formed. -/
theorem list_inv {α : Type} {T : Edition} {wf : α → Bool} {tokens : α → List TokenKind}
    {afterOK : List TokenKind → α → Bool} {close : String} {refuse : Token → ParseM Unit} {p : ParseM α}
    (hp : GivesItem T wf tokens afterOK p) (hrefuse : ∀ t s s', refuse t s = .ok () s' → s' = s)
    {s₁ : ParseState} {n : Nat} {items : Array α} {st : ParseState} (hR : Ready s₁) (hT : s₁.target = T)
    (h : Parse.iterate n #[] (Parse.listStep close refuse p) s₁ = .ok items st) :
    ListSoFar wf tokens afterOK s₁ items st :=
  (iterate_inv (I := ListSoFar wf tokens afterOK s₁)
    (fun _ _ _ _ _ hI hst => listStep_inv hp hrefuse hT hI hst) _ #[] s₁ items st
    ⟨hR, Kept.refl _, ⟨[], by simp, by simp [joined, skel]⟩, by simp, fun _ _ => trivial⟩ h).1

/-- `parseAssign` reads items of a list. -/
theorem GivesE.item {T : Edition} {p : ParseM Expr} (h : GivesE T .assign p) :
    GivesItem T (fun e => e.wfAt T .assign && e.words.all (Word.ok T)) Expr.tokens (fun after e => e.afterOK after) p := by
  intro s x s' hR hT hx
  have g := h _ _ _ hR hT hx
  obtain ⟨src, h1, h2, _⟩ := g.tokens
  exact ⟨g.ready, g.kept, ⟨src, h1, h2⟩, both g.wf g.ok, g.after⟩

theorem refuseArgument_inv (t : Token) (s s' : ParseState) (h : Parse.refuseArgument t s = .ok () s') : s' = s := by
  simp only [Parse.refuseArgument] at h; exact check_inv h

theorem refuseElement_inv (t : Token) (s s' : ParseState) (h : Parse.refuseElement t s = .ok () s') : s' = s := by
  simp only [Parse.refuseElement] at h
  obtain ⟨_, h⟩ := fail_inv h
  exact check_inv h

theorem tokens_args (args : List Expr) :
    (enclose "(" ")" (Expr.wordsOf args)).flatten = .punct "(" :: joined "," (args.map Expr.tokens) ++ [.punct ")"] := by
  simp [enclose, punctWord, separated_flatten, Expr.wordsOf_eq, List.map_map, Function.comp_def]; rfl

/-- What `parseArguments` gave when it read `( args )` from `s` to `s'`. -/
structure GaveArgs (T : Edition) (s : ParseState) (args : List Expr) (s' : ParseState) : Prop where
  ready : Ready s'
  kept : Kept s s'
  tokens : ∃ src, s.rest = src ++ s'.rest ∧
    skel (src.map (·.kind)) = skel (enclose "(" ")" (Expr.wordsOf args)).flatten
  wf : Expr.allWF T args = true
  after : ∀ after, Follows (s'.rest.map (·.kind)) after → Expr.afterOKList (.punct ")" :: after) args = true
  ok : WordsOK T (enclose "(" ")" (Expr.wordsOf args))

def GivesArgs (T : Edition) (p : ParseM (List Expr)) : Prop :=
  ∀ s args s', Ready s → s.target = T → p s = .ok args s' → GaveArgs T s args s'

/-- A bracketed list: its open token, its items and its close token. -/
theorem bracketed {α : Type} {wf : α → Bool} {tokens : α → List TokenKind}
    {afterOK : List TokenKind → α → Bool} {o c : String} {s₁ st s' : ParseState} {items : Array α}
    {lp rp : Token} {r : List Token} (hs : s₁.rest = lp :: r) (hlp : lp.kind = .punct o)
    (hc : c = ")" ∨ c = "]" ∨ c = "}")
    (hL : ListSoFar wf tokens afterOK (past s₁ lp r) items st)
    (hrp : Parse.expectPunct c st = .ok rp s') :
    Ready s' ∧ Kept (past s₁ lp r) s' ∧
      (∃ src, s₁.rest = src ++ s'.rest ∧
        skel (src.map (·.kind)) = skel (.punct o :: joined "," (items.toList.map tokens) ++ [.punct c]) ∧
        (src.map (·.kind)).head? = some (.punct o)) ∧
      (∀ x ∈ items.toList, wf x = true) ∧
      ∀ after, Follows (s'.rest.map (·.kind)) after → ListAfter afterOK tokens (.punct c :: after) items.toList := by
  obtain ⟨hR, hK, ⟨src, h1, h2⟩, hwf, hafter⟩ := hL
  obtain ⟨hrk, r₂, hs₂, rfl, hR₂⟩ := expectPunct_inv hR hrp
  refine ⟨hR₂, hK.trans (Kept.past _ _ _), ⟨lp :: src ++ [rp], ?_, ?_, by simp [hlp]⟩, hwf,
    fun after hf => hafter _ ?_⟩
  · rw [hs, show r = src ++ st.rest from h1, hs₂]; simp
  · simp only [List.map_append, List.map_cons, List.map_nil, skel_append, skel_cons, h2, hlp, hrk,
      List.cons_append]
  · have := hf.prefix (p := [rp.kind]) (p' := [.punct c]) (by rw [hrk]) (by rcases hc with rfl | rfl | rfl <;> simp)
    simpa [hs₂] using this

theorem parseArguments_gives {T : Edition} {f : Nat} (hA : GivesE T .assign (Parse.parseAssign f)) :
    GivesArgs T (Parse.parseArguments (f + 1)) := by
  intro s args s' hR hT h
  simp only [Parse.parseArguments] at h
  rw [Parse.bind_ok] at h; obtain ⟨lp, s₁, hl, h⟩ := h
  obtain ⟨hlk, r, hs, rfl, hR₁⟩ := expectPunct_inv hR hl
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h; obtain ⟨items, st, hit, h⟩ := h
  have hL := list_inv hA.item refuseArgument_inv hR₁ hT hit
  rw [Parse.bind_ok] at h; obtain ⟨rp, s₂, hrp, h⟩ := h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hR₂, hK₂, ⟨src, h1, h2, _⟩, hwf, hafter⟩ := bracketed hs hlk (.inl rfl) hL hrp
  exact ⟨hR₂, (Kept.past _ _ _).trans hK₂, ⟨src, h1, by rw [h2, tokens_args]⟩,
    Expr.allWF_iff.mpr (fun x hx => both_left (hwf x hx)), fun after hf => Expr.afterOKList_of _ (hafter after hf),
    wordsOK_enclose (by decide) (by decide) (Expr.wordsOK_of (fun e he => both_right (hwf e he)))⟩

theorem parseArrayLiteral_gives {T : Edition} {f : Nat} (hA : GivesE T .assign (Parse.parseAssign f)) :
    GivesE T .primary (Parse.parseArrayLiteral (f + 1)) := by
  intro s e s' hR hT h
  simp only [Parse.parseArrayLiteral] at h
  rw [Parse.bind_ok] at h; obtain ⟨lp, s₁, hl, h⟩ := h
  obtain ⟨hlk, r, hs, rfl, hR₁⟩ := expectPunct_inv hR hl
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h; obtain ⟨items, st, hit, h⟩ := h
  have hL := list_inv hA.item refuseElement_inv hR₁ hT hit
  rw [Parse.bind_ok] at h; obtain ⟨rp, s₂, hrp, h⟩ := h
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hR₂, hK₂, ⟨src, h1, h2, h3⟩, hwf, hafter⟩ := bracketed hs hlk (.inr (.inl rfl)) hL hrp
  refine ⟨hR₂, (Kept.past _ _ _).trans hK₂, ⟨src, h1, by rw [h2, Expr.tokens_array], by rw [h3, Expr.tokens_array]; rfl⟩,
    ?_, fun after hf => ?_, by
      simpa [Expr.words] using wordsOK_enclose (T := T) (o := "[") (c := "]") (by decide) (by decide)
        (Expr.wordsOK_of (fun e he => both_right (hwf e he)))⟩
  · simpa [Expr.wfAt] using Expr.allWF_iff.mpr (fun x hx => both_left (hwf x hx))
  · simpa [Expr.afterOK] using Expr.afterOKList_of _ (hafter after hf)

theorem skel_propertyName (n : String) : skel (propertyName n) = [] := by
  unfold propertyName; split <;> simp [keywordWord, identWord, skel, skelKind]

/-- `key : value`, after the key token. -/
theorem keyValue_tail {T : Edition} {f : Nat} (hA : GivesE T .assign (Parse.parseAssign f))
    {s s' : ParseState} {t c : Token} {r r₁ : List Token} {key : PropKey} {q : Property} {start : Pos}
    (hT : s.target = T) (hs : s.rest = t :: r) (hR₁ : Ready (past s t r)) (hs₁ : r = c :: r₁)
    (hc : c.kind = .punct ":") (hkey : skel (PropKey.words key).flatten = []) (ht : skel [t.kind] = [])
    (hkok : WordsOK T key.words)
    (h : (discard Parse.advance >>= fun _ => Parse.parseAssign f >>= fun value =>
      Parse.spanFrom start >>= fun sp => pure (Property.keyValue sp key value)) (past s t r) = .ok q s') :
    Ready s' ∧ Kept s s' ∧ (∃ src, s.rest = src ++ s'.rest ∧ skel (src.map (·.kind)) = skel q.tokens) ∧
      (Property.wf T q && q.words.all (Word.ok T)) = true ∧
      ∀ after, Follows (s'.rest.map (·.kind)) after → q.afterOK after = true := by
  have hne : c.kind ≠ .eof := by rw [hc]; simp
  have hs' : (past s t r).rest = c :: r₁ := hs₁
  rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hs' hne)), Parse.bind_ok] at h
  obtain ⟨value, s₂, hv, h⟩ := h
  have gv := hA _ _ _ (hR₁.past hs' (hR₁.more hs' hne)) hT hv
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨vsrc, hv1, hv2, _⟩ := gv.tokens
  refine ⟨gv.ready, (Kept.past _ _ _).trans ((Kept.past _ _ _).trans gv.kept), ⟨t :: c :: vsrc, ?_, ?_⟩, ?_, ?_⟩
  · rw [hs, hs₁, show r₁ = vsrc ++ s₂.rest from hv1]; rfl
  · simp only [Property.tokens, Property.words, List.flatten_append, List.flatten_cons, List.map_cons,
      skel_append]
    rw [show skel (t.kind :: c.kind :: vsrc.map (·.kind)) = skel [t.kind] ++ skel (c.kind :: vsrc.map (·.kind))
      by rw [← skel_append]; rfl, ht, hkey]
    simp (config := { decide := true }) only [skel_cons, hc, punctWord, hv2, List.nil_append,
      ↓reduceIte, Expr.tokens]
    rfl
  · exact both (by simpa [Property.wf] using gv.wf) (by
      simpa [Property.words, punctWord] using hkok.append (WordsOK.cons (ok_punct (p := ":") (by decide)) gv.ok))
  · intro after hf; simpa [Property.afterOK] using gv.after after hf

theorem parseProperty_gives {T : Edition} {f : Nat} (hA : GivesE T .assign (Parse.parseAssign f)) :
    GivesItem T (fun q => Property.wf T q && q.words.all (Word.ok T)) Property.tokens (fun after q => q.afterOK after)
      (Parse.parseProperty (f + 1)) := by
  intro s q s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseProperty] at h
  rw [Parse.bind_ok] at h; obtain ⟨t, s₁, ha, h⟩ := h
  obtain ⟨rfl, hpast⟩ := advance_inv hR hs ha
  have htok : t.kind ≠ .eof → Word.ok T [t.kind] = true := fun hne => hT ▸ hR.tok (by simp [hs]) hne
  generalize hk : t.kind = k at h hpast htok
  cases k with
  | ident name =>
    obtain ⟨rfl, hR₁⟩ := hpast (by simp)
    simp only at h
    obtain ⟨n, r₁, hs₁⟩ := hR₁.cons
    rw [Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₁)] at h
    by_cases hc : n.isPunct ":" = true
    · rw [if_pos hc] at h
      exact keyValue_tail hA hT hs hR₁ hs₁ (by simpa [Token.isPunct] using hc)
        (by simpa [PropKey.words] using skel_propertyName name) (by rw [hk]; simp [skel, skelKind])
        (key := .ident name) (WordsOK.word (propertyName_ok (.inl rfl) (htok (by simp)))) h
    rw [if_neg hc, Parse.pure_bind] at h
    by_cases hcl : (n.isPunct "," || n.isPunct "}") = true
    · rw [if_pos hcl] at h
      by_cases hrf : Parse.refusedNames.contains name = true
      · rw [if_pos hrf] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)
      rw [if_neg hrf, Parse.pure_bind] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨hR₁, Kept.past _ _ _, ⟨[t], by simpa using hs, ?_⟩, ?_, fun _ _ => by simp [Property.afterOK]⟩
      · simp [Property.tokens, Property.words, identWord, hk, skel, skelKind]
      · exact both (by simpa [Property.wf, exprName] using hrf)
          (by simpa [Property.words, identWord] using WordsOK.word (htok (by simp)))
    rw [if_neg hcl, Parse.pure_bind] at h
    obtain ⟨_, h⟩ := fail_inv h
    exact absurd h (Parse.unexpected_ne_ok _ _ _ _ _)
  | keyword name =>
    obtain ⟨rfl, hR₁⟩ := hpast (by simp)
    simp only at h
    obtain ⟨n, r₁, hs₁⟩ := hR₁.cons
    rw [Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₁)] at h
    by_cases hc : n.isPunct ":" = true
    · rw [if_pos hc] at h
      exact keyValue_tail hA hT hs hR₁ hs₁ (by simpa [Token.isPunct] using hc)
        (by simpa [PropKey.words] using skel_propertyName name) (by rw [hk]; simp [skel, skelKind])
        (key := .ident name) (WordsOK.word (propertyName_ok (.inr rfl) (htok (by simp)))) h
    rw [if_neg hc, Parse.pure_bind] at h
    by_cases hcl : (n.isPunct "," || n.isPunct "}") = true
    · rw [if_pos hcl] at h; exact absurd h (Parse.unexpected_ne_ok _ _ _ _ _)
    rw [if_neg hcl, Parse.pure_bind] at h
    obtain ⟨_, h⟩ := fail_inv h
    exact absurd h (Parse.unexpected_ne_ok _ _ _ _ _)
  | string v | number v =>
    obtain ⟨rfl, hR₁⟩ := hpast (by simp)
    simp only at h
    obtain ⟨n, r₁, hs₁⟩ := hR₁.cons
    rw [Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₁)] at h
    by_cases hc : n.isPunct ":" = true
    · rw [if_pos hc] at h
      exact keyValue_tail hA hT hs hR₁ hs₁ (by simpa [Token.isPunct] using hc)
        (by simp [PropKey.words, skel, skelKind]) (by rw [hk]; simp [skel, skelKind])
        (by simpa [PropKey.words] using WordsOK.word (htok (by simp))) h
    rw [if_neg hc, Parse.pure_bind] at h
    by_cases hcl : (n.isPunct "," || n.isPunct "}") = true
    · rw [if_pos hcl] at h; exact absurd h (Parse.unexpected_ne_ok _ _ _ _ _)
    rw [if_neg hcl, Parse.pure_bind] at h
    obtain ⟨_, h⟩ := fail_inv h
    exact absurd h (Parse.unexpected_ne_ok _ _ _ _ _)
  | punct p =>
    by_cases h1 : p = "["
    · subst h1; simp at h
    by_cases h2 : p = "..."
    · subst h2; simp at h
    simp [h1, h2] at h
  | _ => simp at h

theorem parseObjectLiteral_gives {T : Edition} {f : Nat}
    (hP : GivesItem T (fun q => Property.wf T q && q.words.all (Word.ok T)) Property.tokens
      (fun after q => q.afterOK after) (Parse.parseProperty f)) :
    GivesE T .primary (Parse.parseObjectLiteral (f + 1)) := by
  intro s e s' hR hT h
  simp only [Parse.parseObjectLiteral] at h
  rw [Parse.bind_ok] at h; obtain ⟨lp, s₁, hl, h⟩ := h
  obtain ⟨hlk, r, hs, rfl, hR₁⟩ := expectPunct_inv hR hl
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h; obtain ⟨items, st, hit, h⟩ := h
  have hL := list_inv hP (fun _ _ _ h' => by simp only [Parse.pure_ok] at h'; exact h'.2.symm) hR₁ hT hit
  rw [Parse.bind_ok] at h; obtain ⟨rp, s₂, hrp, h⟩ := h
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hR₂, hK₂, ⟨src, h1, h2, h3⟩, hwf, hafter⟩ := bracketed hs hlk (.inr (.inr rfl)) hL hrp
  refine ⟨hR₂, (Kept.past _ _ _).trans hK₂, ⟨src, h1, by rw [h2, Expr.tokens_object], by rw [h3, Expr.tokens_object]; rfl⟩,
    ?_, fun after hf => ?_, by
      simpa [Expr.words] using wordsOK_enclose (T := T) (o := "{") (c := "}") (by decide) (by decide)
        (Property.wordsOK_of (fun e he => both_right (hwf e he)))⟩
  · simpa [Expr.wfAt] using Property.allWF_iff.mpr (fun x hx => both_left (hwf x hx))
  · simpa [Expr.afterOK] using Property.afterOKList_of _ (hafter after hf)

/-! ### Primary expressions and left-hand sides -/

/-- A primary expression of one token. -/
theorem leaf_gives {T : Edition} {s : ParseState} {x : Token} {r : List Token} {e : Expr}
    (hs : s.rest = x :: r) (hR₁ : Ready (past s x r)) (htok : e.tokens = [x.kind])
    (hw : e.wfAt T .primary = true) (ha : ∀ after, e.afterOK after = true) (hwd : WordsOK T e.words) :
    GaveE T .primary s e (past s x r) :=
  ⟨hR₁, Kept.past _ _ _, ⟨[x], by simpa using hs, by rw [htok]; rfl, by rw [htok]; rfl⟩, hw, fun after _ => ha after,
    hwd⟩

/-- What `parseNew` gives when it reads from a `new`. -/
def GivesNew (T : Edition) (p : ParseM Expr) : Prop :=
  ∀ s e s', Ready s → s.target = T → p s = .ok e s' →
    ∀ x r, s.rest = x :: r → x.kind = .keyword "new" → GaveE T .primary s e s'

/-- The tokens of a type reference do not depend on its span. -/
theorem tokens_ref_span (sp sp' : Span) (c : String) (ts : List TypeExpr) :
    (TypeExpr.ref sp c ts).tokens = (TypeExpr.ref sp' c ts).tokens := by
  cases ts <;> rfl

theorem parseNew_gives {T : Edition} {f : Nat} (hArgs : GivesArgs T (Parse.parseArguments f)) :
    GivesNew T (Parse.parseNew (f + 1)) := by
  intro s e s' hR hT h x r hs hx
  simp only [Parse.parseNew] at h
  rw [Parse.bind_ok] at h; obtain ⟨t, s₁, ha, h⟩ := h
  obtain ⟨rfl, hpast⟩ := advance_inv hR hs ha
  obtain ⟨rfl, hR₁⟩ := hpast (by rw [hx]; simp)
  rw [Parse.bind_eq (peek_eq' _)] at h
  obtain ⟨-, h⟩ := fail_inv h
  rw [Parse.bind_eq (Parse.peekAt_rest _ _)] at h
  obtain ⟨-, h⟩ := fail_inv h
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h; obtain ⟨ty, s₂, hty, h⟩ := h
  have hT₁ : (past s t r).target = T := hT
  obtain ⟨gT1, hR₂, hK₂⟩ := (types_give T _).2.2 _ _ _ hR₁ hT₁ hty
  obtain ⟨-, hS₂⟩ := (types_skel _).2.2 _ _ _ hR₁ hty
  cases ty with
  | ref sp c targs =>
    simp only at h
    rw [Parse.bind_eq (peek_eq' _)] at h
    obtain ⟨-, h⟩ := fail_inv h
    rw [Parse.bind_ok] at h; obtain ⟨args, s₃, hpa, h⟩ := h
    have gA := hArgs _ _ _ hR₂ (hK₂.target_eq.trans hT₁) hpa
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    have hwT : (TypeExpr.ref sp c targs).primaryWF = true := both_left gT1
    have hoT : WordsOK T (TypeExpr.ref sp c targs).words := both_right gT1
    obtain ⟨srcT, hT1, hT2⟩ := hS₂
    obtain ⟨srcA, hA1, hA2⟩ := gA.tokens
    have hw : (Expr.new ⟨t.span.start, s₃.lastStop⟩ c targs args).words =
        keywordWord "new" :: (TypeExpr.ref sp c targs).words ++ enclose "(" ")" (Expr.wordsOf args) := by
      rw [← typeArgWords_ref sp c targs]; rfl
    refine ⟨gA.ready, (Kept.past _ _ _).trans (hK₂.trans gA.kept), ⟨t :: (srcT ++ srcA), ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hs]; simp [show r = srcT ++ s₂.rest from hT1, hA1]
    · rw [Expr.tokens_new (sp := ⟨t.span.start, s₃.lastStop⟩) c targs args, tokens_ref_span _ sp]
      simp only [List.map_cons, List.map_append, skel_cons, skel_append, hx, hT2, hA2, tokens_args]
      simp [skelKind]
    · rw [Expr.tokens_new]; simp [hx]
    · simp only [TypeExpr.primaryWF, Bool.and_eq_true] at hwT
      simp [Expr.wfAt, hwT.1, hwT.2, gA.wf]
    · intro after hf; simpa [Expr.afterOK] using gA.after after hf
    · rw [hw]; exact WordsOK.cons (ok_keyword (by decide)) (hoT.append gA.ok)
  | _ => simp only at h; exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)

theorem parsePrimary_gives {T : Edition} {f : Nat} (hE : GivesE T .assign (Parse.parseExpression f))
    (hArr : GivesE T .primary (Parse.parseArrayLiteral f)) (hObj : GivesE T .primary (Parse.parseObjectLiteral f))
    (hNew : GivesNew T (Parse.parseNew f)) :
    GivesE T .primary (Parse.parsePrimary (f + 1)) := by
  intro s e s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parsePrimary] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  have hadv : x.kind ≠ .eof → Ready (past s x r) := fun hx => hR.past hs (hR.more hs hx)
  have htok : x.kind ≠ .eof → Word.ok T [x.kind] = true := fun hne => hT ▸ hR.tok (by simp [hs]) hne
  generalize hk : x.kind = k at h hadv
  cases k with
  | ident n =>
    simp only at h
    rw [Parse.bind_ok] at h; obtain ⟨name, s₁, hn, h⟩ := h
    obtain ⟨t, r', htk, hnr, hs', rfl, hR₁⟩ := readName_inv hR hn
    rw [hs] at hs'; simp only [List.cons.injEq] at hs'; obtain ⟨rfl, rfl⟩ := hs'
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact leaf_gives hs hR₁ (by simp [Expr.tokens, Expr.words, identWord, htk])
      (by simpa [Expr.wfAt, exprName] using hnr) (fun _ => by simp [Expr.afterOK])
      (by simpa [Expr.words, WordsOK, identWord, htk] using htok (by simp [htk]))
  | number v | bigint v | string v =>
    simp only at h
    rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs (by rw [hk]; simp)))] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact leaf_gives hs (hadv (by simp)) (by simp [Expr.tokens, Expr.words, hk]) (by simp [Expr.wfAt])
      (fun _ => by simp [Expr.afterOK]) (by simpa [Expr.words, WordsOK, hk] using htok (by simp [hk]))
  | keyword w =>
    by_cases h1 : w = "true"
    · subst h1; simp only at h
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs (by rw [hk]; simp)))] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      exact leaf_gives hs (hadv (by simp)) (by simp [Expr.tokens, Expr.words, keywordWord, hk])
        (by simp [Expr.wfAt]) (fun _ => by simp [Expr.afterOK])
        (by simpa [Expr.words, WordsOK, keywordWord, hk] using htok (by simp [hk]))
    by_cases h2 : w = "false"
    · subst h2; simp only at h
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs (by rw [hk]; simp)))] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      exact leaf_gives hs (hadv (by simp)) (by simp [Expr.tokens, Expr.words, keywordWord, hk])
        (by simp [Expr.wfAt]) (fun _ => by simp [Expr.afterOK])
        (by simpa [Expr.words, WordsOK, keywordWord, hk] using htok (by simp [hk]))
    by_cases h3 : w = "null"
    · subst h3; simp only at h
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs (by rw [hk]; simp)))] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      exact leaf_gives hs (hadv (by simp)) (by simp [Expr.tokens, Expr.words, keywordWord, hk])
        (by simp [Expr.wfAt]) (fun _ => by simp [Expr.afterOK])
        (by simpa [Expr.words, WordsOK, keywordWord, hk] using htok (by simp [hk]))
    by_cases h4 : w = "new"
    · subst h4; simp only at h; exact hNew _ _ _ hR hT h x r hs hk
    simp at h
  | punct p =>
    by_cases h1 : p = "("
    · subst h1; simp only at h
      have hR₁ := hadv (by simp)
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs (by rw [hk]; simp))), Parse.bind_ok] at h
      obtain ⟨inner, s₁, hi, h⟩ := h
      have gi := hE _ _ _ hR₁ hT hi
      rw [Parse.bind_ok] at h; obtain ⟨rp, s₂, hrp, h⟩ := h
      obtain ⟨hrk, r₂, hs₂, rfl, hR₂⟩ := expectPunct_inv gi.ready hrp
      rw [Parse.bind_ok] at h; obtain ⟨_, s₃, hra, h⟩ := h
      obtain rfl := refuseArrowLookalike_inv hra
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨isrc, hi1, hi2, _⟩ := gi.tokens
      refine ⟨hR₂, (Kept.past _ _ _).trans (gi.kept.trans (Kept.past _ _ _)), ⟨x :: isrc ++ [rp], ?_, ?_, ?_⟩,
        ?_, ?_, (by
          simpa [Expr.words, punctWord] using WordsOK.cons (ok_punct (T := T) (p := "(") (by decide))
            (gi.ok.append (WordsOK.word (ok_punct (p := ")") (by decide)))))⟩
      · rw [hs, show r = isrc ++ s₁.rest from hi1, hs₂]; simp
      · rw [Expr.tokens_paren]
        simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, skel_cons, skel_append, hi2,
          hk, hrk]
      · rw [Expr.tokens_paren]; simp [hk]
      · simpa [Expr.wfAt] using gi.wf
      · intro after hf
        simp only [Expr.afterOK, Bool.and_eq_true, notFirst, bne_iff_ne, ne_eq]
        refine ⟨hf.2, gi.after _ ?_⟩
        have := hf.prefix (p := [rp.kind]) (p' := [.punct ")"]) (by rw [hrk]) (by simp)
        simpa [hs₂] using this
    by_cases h2 : p = "["
    · subst h2; simp only at h; exact hArr _ _ _ hR hT h
    by_cases h3 : p = "{"
    · subst h3; simp only at h; exact hObj _ _ _ hR hT h
    simp [h1, h2, h3] at h
  | eof => simp at h

/-- A check that keeps the state, run or not by an `if`, keeps the state. -/
theorem seq_same {c : Prop} {a : ParseM PUnit} {s s₁ : ParseState} (h1 : c → a s = .ok () s₁) (h2 : ¬c → s₁ = s)
    (ha : ∀ s s', a s = .ok () s' → s' = s) : s₁ = s := by
  by_cases hc : c
  · exact ha _ _ (h1 hc)
  · exact h2 hc

theorem skel_one {p : String} (h : skelKind (.punct p) = false) : skel [.punct p] = [] := by
  simp [skel, h]

theorem lhsStep_inv {T : Edition} {f : Nat} {start : Pos} (hE : GivesE T .assign (Parse.parseExpression f))
    (hA : GivesArgs T (Parse.parseArguments f)) {s₀ : ParseState} {acc acc' : Expr} {b : Bool}
    {st st' : ParseState} (hT : s₀.target = T) (g : GaveE T .lhs s₀ acc st)
    (h : Parse.leftHandSideStep (Parse.parseExpression f) (Parse.parseArguments f) start acc st = .ok (acc', b) st') :
    GaveE T .lhs s₀ acc' st' := by
  have hR := g.ready
  have hTs : st.target = T := g.kept.target_eq.trans hT
  obtain ⟨x, r, hs⟩ := hR.cons
  obtain ⟨src, hg1, hg2, hg3⟩ := g.tokens
  simp only [Parse.leftHandSideStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hdot : x.isPunct "." = true
  · rw [if_pos hdot] at h
    have hxk : x.kind = .punct "." := by simpa [Token.isPunct] using hdot
    have hne : x.kind ≠ .eof := by rw [hxk]; simp
    have hR₁ := hR.past hs (hR.more hs hne)
    rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)), Parse.bind_ok] at h
    obtain ⟨_, s₁, hsm, h⟩ := h
    obtain rfl := refuseSplitMember_inv hsm
    rw [Parse.bind_ok] at h; obtain ⟨name, s₂, hn, h⟩ := h
    obtain ⟨nm, r₂, hnk, hs₂, rfl, hR₂⟩ := readPropertyName_inv hR₁ hn
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    have hskn : skel [nm.kind] = [] := by rcases hnk with h' | h' <;> simp [h', skel, skelKind]
    have hdot0 : skel [TokenKind.punct "."] = [] := skel_one (by decide)
    have hx1 : skel [x.kind, nm.kind] = [] := by
      rw [show [x.kind, nm.kind] = [x.kind] ++ [nm.kind] from rfl, skel_append, hskn, hxk, hdot0]; rfl
    have hx2 : skel (.punct "." :: propertyName name) = [] := by
      rw [show (TokenKind.punct "." :: propertyName name) = [.punct "."] ++ propertyName name from rfl, skel_append,
        hdot0, skel_propertyName]; rfl
    have hnmok : Word.ok T [nm.kind] = true := hTs ▸ hR₁.tok (s := past st x r)
      (by rw [show r = nm :: r₂ from hs₂]; simp)
      (by rcases hnk with h' | h' <;> rw [h'] <;> simp)
    refine ⟨hR₂, g.kept.trans ((Kept.past _ _ _).trans (Kept.past _ _ _)), ⟨src ++ [x, nm], ?_, ?_, ?_⟩, ?_, ?_,
      by simpa [Expr.words, punctWord] using g.ok.append (WordsOK.cons (ok_punct (p := ".") (by decide))
        (WordsOK.word (propertyName_ok hnk hnmok)))⟩
    · rw [hg1, hs, show r = nm :: r₂ from hs₂]; simp
    · rw [Expr.tokens_member]
      simp only [List.map_append, skel_append, hg2]
      rw [show [x, nm].map (·.kind) = [x.kind, nm.kind] from rfl, hx1, hx2]
    · rw [Expr.tokens_member]; exact head_append2 (Expr.tokens_ne_nil acc) hg3
    · simpa [Expr.wfAt] using g.wf
    · intro after hf
      simp only [Expr.afterOK]
      apply g.after
      have := hf.prefix (p := [x.kind, nm.kind]) (p' := .punct "." :: propertyName name)
        (by rw [hx1, hx2]) (by simp)
      simpa [hs, show r = nm :: r₂ from hs₂] using this
  rw [if_neg hdot] at h
  by_cases hlb : x.isPunct "[" = true
  · rw [if_pos hlb] at h
    have hxk : x.kind = .punct "[" := by simpa [Token.isPunct] using hlb
    have hne : x.kind ≠ .eof := by rw [hxk]; simp
    have hR₁ := hR.past hs (hR.more hs hne)
    rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)), Parse.bind_ok] at h
    obtain ⟨idx, s₁, hi, h⟩ := h
    have gi := hE _ _ _ hR₁ hTs hi
    rw [Parse.bind_ok] at h; obtain ⟨rb, s₂, hrb, h⟩ := h
    obtain ⟨hrk, r₂, hs₂, rfl, hR₂⟩ := expectPunct_inv gi.ready hrb
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    obtain ⟨isrc, hi1, hi2, _⟩ := gi.tokens
    have hr : r = isrc ++ rb :: r₂ := by rw [show r = isrc ++ s₁.rest from hi1, hs₂]
    refine ⟨hR₂, g.kept.trans ((Kept.past _ _ _).trans (gi.kept.trans (Kept.past _ _ _))),
      ⟨src ++ x :: isrc ++ [rb], ?_, ?_, ?_⟩, ?_, ?_, by
        simpa [Expr.words, punctWord] using g.ok.append (WordsOK.cons (ok_punct (p := "[") (by decide))
          (gi.ok.append (WordsOK.word (ok_punct (p := "]") (by decide)))))⟩
    · rw [hg1, hs, hr]; simp
    · rw [Expr.tokens_index, List.append_assoc]
      simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, skel_append, skel_cons, hg2, hi2,
        hxk, hrk, List.append_assoc]
    · rw [Expr.tokens_index, List.append_assoc, List.append_assoc]; exact head_append2 (Expr.tokens_ne_nil acc) hg3
    · simp only [Expr.wfAt, Bool.and_eq_true]; exact ⟨g.wf, gi.wf⟩
    · intro after hf
      simp only [Expr.afterOK, Bool.and_eq_true]
      have hfi : Follows ((rb :: r₂).map (·.kind)) (.punct "]" :: after) := by
        have := hf.prefix (p := [rb.kind]) (p' := [.punct "]"]) (by rw [hrk]) (by simp)
        simpa using this
      refine ⟨g.after _ ?_, gi.after _ (by rw [hs₂]; exact hfi)⟩
      have := hfi.prefix (p := (x :: isrc).map (·.kind)) (p' := .punct "[" :: idx.tokens)
        (by simp only [List.map_cons, skel_cons, hxk, hi2]) (by simp)
      simpa [hs, hr, List.append_assoc] using this
  rw [if_neg hlb] at h
  by_cases hlp : x.isPunct "(" = true
  · rw [if_pos hlp, Parse.bind_ok] at h
    obtain ⟨args, s₁, ha, h⟩ := h
    have ga := hA _ _ _ hR hTs ha
    obtain ⟨s₂, hy1, hy2, h⟩ := seq_inv h
    have e2 : s₂ = s₁ := seq_same hy1 hy2 (fun _ _ h' => refuseAsyncArrowLookalike_inv h')
    rw [e2, Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    obtain ⟨asrc, ha1, ha2⟩ := ga.tokens
    refine ⟨ga.ready, g.kept.trans ga.kept, ⟨src ++ asrc, ?_, ?_, ?_⟩, ?_, ?_,
      by simpa [Expr.words, List.append_assoc] using g.ok.append ((wordsOK_callBreak acc).append ga.ok)⟩
    · rw [hg1, ha1]; simp
    · rw [Expr.tokens_call, List.append_assoc, ← tokens_args]; simp only [List.map_append, skel_append, hg2, ha2]
    · rw [Expr.tokens_call, List.append_assoc, ← tokens_args]; exact head_append2 (Expr.tokens_ne_nil acc) hg3
    · simp only [Expr.wfAt, Bool.and_eq_true]; exact ⟨g.wf, ga.wf⟩
    · intro after hf
      simp only [Expr.afterOK, Bool.and_eq_true]
      refine ⟨g.after _ ?_, ga.after _ hf⟩
      have := hf.prefix (p := asrc.map (·.kind)) (p' := (enclose "(" ")" (Expr.wordsOf args)).flatten) ha2
        (by rw [tokens_args]; simp)
      simpa [ha1] using this
  rw [if_neg hlp] at h
  by_cases hq : x.isPunct "?." = true
  · rw [if_pos hq, Parse.bind_ok] at h
    obtain ⟨_, s₀, hrf, h⟩ := h
    obtain ⟨hs₀, hsup⟩ := requireFeature_inv hrf
    rw [hs₀] at h
    have hxk : x.kind = .punct "?." := by simpa [Token.isPunct] using hq
    have hne : x.kind ≠ .eof := by rw [hxk]; simp
    have hR₁ := hR.past hs (hR.more hs hne)
    rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)), Parse.bind_ok] at h
    obtain ⟨_, s₁, hsm, h⟩ := h
    obtain rfl := refuseSplitMember_inv hsm
    rw [Parse.bind_ok] at h; obtain ⟨name, s₂, hn, h⟩ := h
    obtain ⟨nm, r₂, hnk, hs₂, rfl, hR₂⟩ := readPropertyName_inv hR₁ hn
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    have hskn : skel [nm.kind] = [] := by rcases hnk with h' | h' <;> simp [h', skel, skelKind]
    have hdot0 : skel [TokenKind.punct "?."] = [] := skel_one (by decide)
    have hx1 : skel [x.kind, nm.kind] = [] := by
      rw [show [x.kind, nm.kind] = [x.kind] ++ [nm.kind] from rfl, skel_append, hskn, hxk, hdot0]; rfl
    have hx2 : skel (.punct "?." :: propertyName name) = [] := by
      rw [show (TokenKind.punct "?." :: propertyName name) = [.punct "?."] ++ propertyName name from rfl,
        skel_append, hdot0, skel_propertyName]; rfl
    have hnmok : Word.ok T [nm.kind] = true := hTs ▸ hR₁.tok (s := past st x r)
      (by rw [show r = nm :: r₂ from hs₂]; simp)
      (by rcases hnk with h' | h' <;> rw [h'] <;> simp)
    refine ⟨hR₂, g.kept.trans ((Kept.past _ _ _).trans (Kept.past _ _ _)), ⟨src ++ [x, nm], ?_, ?_, ?_⟩, ?_, ?_,
      by simpa [Expr.words, punctWord] using g.ok.append (WordsOK.cons (ok_punct (p := "?.") (by decide))
        (WordsOK.word (propertyName_ok hnk hnmok)))⟩
    · rw [hg1, hs, show r = nm :: r₂ from hs₂]; simp
    · rw [Expr.tokens_optMember]
      simp only [List.map_append, skel_append, hg2]
      rw [show [x, nm].map (·.kind) = [x.kind, nm.kind] from rfl, hx1, hx2]
    · rw [Expr.tokens_optMember]; exact head_append2 (Expr.tokens_ne_nil acc) hg3
    · simp only [Expr.wfAt, Bool.and_eq_true]; exact ⟨hTs ▸ hsup, g.wf⟩
    · intro after hf
      simp only [Expr.afterOK]
      apply g.after
      have := hf.prefix (p := [x.kind, nm.kind]) (p' := .punct "?." :: propertyName name)
        (by rw [hx1, hx2]) (by simp)
      simpa [hs, show r = nm :: r₂ from hs₂] using this
  rw [if_neg hq] at h
  by_cases hb : (x.isPunct "!" && !x.newlineBefore) = true
  · rw [if_pos hb] at h; exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)
  rw [if_neg hb] at h
  simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
  exact g

theorem parseLeftHandSide_gives {T : Edition} {f : Nat} (hE : GivesE T .assign (Parse.parseExpression f))
    (hA : GivesArgs T (Parse.parseArguments f)) (hP : GivesE T .primary (Parse.parsePrimary f)) :
    GivesE T .lhs (Parse.parseLeftHandSide (f + 1)) := by
  intro s e s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseLeftHandSide] at h
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
  obtain ⟨p, s₁, hp, h⟩ := h
  have gp := (hP _ _ _ hR hT hp).lift wfAt_lhs_of_primary
  exact (iterate_inv (I := fun a st => GaveE T .lhs s a st)
    (fun _ _ _ _ _ hI hst => lhsStep_inv hE hA hT hI hst) _ p s₁ e s' gp h).1

/-! #### The words of printed lines -/

theorem wordsOK_append_iff {T : Edition} {a b : List Word} : WordsOK T (a ++ b) ↔ WordsOK T a ∧ WordsOK T b := by
  simp [WordsOK, or_imp, forall_and]

theorem wordsOK_cons_iff {T : Edition} {w : Word} {ws : List Word} :
    WordsOK T (w :: ws) ↔ Word.ok T w = true ∧ WordsOK T ws := by
  simp [WordsOK]

theorem wordsOK_nil_iff {T : Edition} : WordsOK T [] ↔ True := by simp [WordsOK]

/-- Closes `Word.ok T w = true` for a word of fixed keywords, names, punctuators and strings. -/
macro "word_ok" : tactic =>
  `(tactic| (simp only [keywordWord, punctWord, identWord, Word.ok, TokenKind.ok] <;> decide))

/-- Splits `WordsOK T ws` into its words, and closes each from a hypothesis or as a fixed word. -/
macro "words_ok" : tactic => `(tactic| (
  try simp only [wordsOK_append_iff, wordsOK_cons_iff, wordsOK_nil_iff, and_true, true_and]
  all_goals (repeat' apply And.intro)
  all_goals first | assumption | trivial | word_ok))

/-- The name that `readName` read lexes back. -/
theorem readName_words {T : Edition} {s s' : ParseState} {n : String} (h : Ready s) (hT : s.target = T)
    (he : Parse.readName s = .ok n s') : Word.ok T (identWord n) = true := by
  obtain ⟨t, r, htk, _, hs, _, _⟩ := readName_inv h he
  have := hT ▸ h.tok (x := t) (by simp [hs]) (by simp [htk])
  simpa [identWord, htk] using this

theorem typeAnnotation_ok {T : Edition} {a : Option TypeExpr} (ht : ∀ t, a = some t → WordsOK T t.words) :
    WordsOK T (typeAnnotation a) := by
  cases a with
  | none => exact WordsOK.nil
  | some t => have := ht t rfl; simp only [typeAnnotation]; words_ok

theorem optionalMark_ok {T : Edition} : ∀ o : Bool, WordsOK T (optionalMark o)
  | false => WordsOK.nil
  | true => WordsOK.word (ok_punct (by decide))

theorem Param.wordsOK {T : Edition} (p : Param) (hn : Word.ok T (identWord p.name) = true)
    (ht : ∀ t, p.type = some t → WordsOK T t.words) : WordsOK T p.words := by
  have h1 := typeAnnotation_ok ht
  unfold Param.words
  exact WordsOK.cons hn ((optionalMark_ok p.optional).append h1)

/-- What `readOptionalMark` reads: nothing, or a `?` where an optional
parameter may stand. -/
theorem readOptionalMark_inv {ok b : Bool} {s s' : ParseState} (hR : Ready s)
    (h : Parse.readOptionalMark ok s = .ok b s') :
    (b = false ∧ s' = s) ∨
      (b = true ∧ ok = true ∧ ∃ q r, s.rest = q :: r ∧ q.kind = .punct "?" ∧ s' = past s q r ∧ Ready s') := by
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.readOptionalMark] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hq : x.isPunct "?" = true
  · have hk : x.kind = .punct "?" := by simpa [Token.isPunct] using hq
    have hne : x.kind ≠ .eof := by rw [hk]; simp
    rw [if_pos hq] at h
    obtain ⟨hok, h⟩ := fail_inv h
    rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne))] at h
    simp only [Parse.pure_ok] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨rfl, by simpa using hok, x, r, hs, hk, rfl, hR.past hs (hR.more hs hne)⟩
  · rw [if_neg hq] at h
    cases h
    exact .inl ⟨rfl, rfl⟩

/-- After a name, `readOptionalMark` leaves a ready state, and reads the
skeleton of the `?` it gives. -/
theorem readOptionalMark_past {ok b : Bool} {s s' : ParseState} (hR : Ready s)
    (h : Parse.readOptionalMark ok s = .ok b s') :
    Ready s' ∧ Kept s s' ∧ PastSkel s s' (skel (optionalMark b).flatten) ∧ (ok = false → b = false) := by
  rcases readOptionalMark_inv hR h with ⟨rfl, rfl⟩ | ⟨rfl, hok, q, r, hq1, hq2, rfl, hR'⟩
  · exact ⟨hR, Kept.refl _, (PastSkel.refl _).of_eq (by simp [optionalMark, skel]), fun _ => rfl⟩
  · exact ⟨hR', Kept.past _ _ _, (PastSkel.tok hq1).of_eq (by simp [optionalMark, punctWord, hq2]),
      by simp [hok]⟩

/-- What a parser of items that hold no expression gives: an item that `P` accepts. -/
def GivesW {α : Type} (T : Edition) (P : α → Prop) (p : ParseM α) : Prop :=
  ∀ s x s', Ready s → s.target = T → p s = .ok x s' → Ready s' ∧ Kept s s' ∧ P x

theorem parseParam_wf {T : Edition} {ok : Bool} :
    GivesW T (fun p : Param => Param.wf p = true ∧ WordsOK T p.words) (Parse.parseParam ok) := by
  intro s p s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseParam] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  obtain ⟨_, h⟩ := fail_inv h
  obtain ⟨_, h⟩ := fail_inv h
  obtain ⟨_, h⟩ := fail_inv h
  rw [Parse.bind_ok] at h; obtain ⟨name, s₁, hn, h⟩ := h
  have hnok := readName_words hR hT hn
  obtain ⟨tn, r₁, _, hnr, _, rfl, hR₀⟩ := readName_inv hR hn
  have hname : exprName name = true := by simpa [exprName] using hnr
  rw [Parse.bind_ok] at h; obtain ⟨b, s₁, hm, h⟩ := h
  obtain ⟨hR₁, hK₁, -, -⟩ := readOptionalMark_past hR₀ hm
  have hT₁ : s₁.target = T := hK₁.target_eq.trans hT
  obtain ⟨y, r₂, hs₂⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
  by_cases hc : y.isPunct ":" = true
  · have hne : y.kind ≠ .eof := by simp [Token.isPunct] at hc; rw [hc]; simp
    rw [if_pos hc, Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hs₂ hne)), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_ok] at h
    obtain ⟨ty, s₂, hty, h⟩ := h
    obtain ⟨htwo, hR₂, hK₂⟩ := (types_give T _).1 _ _ _ (hR₁.past hs₂ (hR₁.more hs₂ hne)) hT₁ hty
    have htw := both_left htwo
    rw [Parse.pure_bind] at h
    obtain ⟨z, r₃, hs₃⟩ := hR₂.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₃)] at h
    obtain ⟨_, h⟩ := fail_inv h
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR₂, (Kept.past _ _ _).trans (hK₁.trans ((Kept.past _ _ _).trans hK₂)), by simp [Param.wf, hname, htw],
      Param.wordsOK _ hnok (fun t ht => by simp at ht; subst ht; exact both_right htwo)⟩
  · rw [if_neg hc, Parse.pure_bind] at h
    rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
    obtain ⟨_, h⟩ := fail_inv h
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR₁, (Kept.past _ _ _).trans hK₁, by simp [Param.wf, hname],
      Param.wordsOK _ hnok (fun t ht => by simp at ht)⟩

/-- An arrow function's parameter is never optional. -/
theorem parseParam_notOptional {s s' : ParseState} {p : Param} (hR : Ready s)
    (h : Parse.parseParam false s = .ok p s') : p.optional = false := by
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseParam] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  obtain ⟨_, h⟩ := fail_inv h
  obtain ⟨_, h⟩ := fail_inv h
  obtain ⟨_, h⟩ := fail_inv h
  rw [Parse.bind_ok] at h; obtain ⟨name, s₁, hn, h⟩ := h
  obtain ⟨tn, r₁, _, _, _, rfl, hR₀⟩ := readName_inv hR hn
  rw [Parse.bind_ok] at h; obtain ⟨b, s₁, hm, h⟩ := h
  obtain ⟨hR₁, -, -, hb⟩ := readOptionalMark_past hR₀ hm
  have hb' := hb rfl
  subst hb'
  obtain ⟨y, r₂, hs₂⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
  by_cases hc : y.isPunct ":" = true
  · have hne : y.kind ≠ .eof := by simp [Token.isPunct] at hc; rw [hc]; simp
    rw [if_pos hc, Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hs₂ hne)), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_ok] at h
    obtain ⟨ty, s₂, hty, h⟩ := h
    obtain ⟨-, hR₂, -⟩ := (types_give _ _).1 _ _ _ (hR₁.past hs₂ (hR₁.more hs₂ hne)) rfl hty
    rw [Parse.pure_bind] at h
    obtain ⟨z, r₃, hs₃⟩ := hR₂.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₃)] at h
    obtain ⟨_, h⟩ := fail_inv h
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    rfl
  · rw [if_neg hc, Parse.pure_bind] at h
    rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
    obtain ⟨_, h⟩ := fail_inv h
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    rfl

/-! ### Arrow functions -/

/-- `parseParam` reads tokens with the skeleton of the printed parameter. -/
theorem parseParam_skel {ok : Bool} {s s' : ParseState} {p : Param} (hR : Ready s)
    (h : Parse.parseParam ok s = .ok p s') :
    PastSkel s s' (skel p.words.flatten) := by
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseParam] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  obtain ⟨_, h⟩ := fail_inv h
  obtain ⟨_, h⟩ := fail_inv h
  obtain ⟨_, h⟩ := fail_inv h
  rw [Parse.bind_ok] at h; obtain ⟨name, s₁, hn, h⟩ := h
  obtain ⟨tn, r₁, htk, _, hs₀, rfl, hR₀⟩ := readName_inv hR hn
  have hP₀ : PastSkel s (past s tn r₁) [] := (PastSkel.tok hs₀).of_eq (by rw [htk]; rfl)
  rw [Parse.bind_ok] at h; obtain ⟨b, s₁, hm, h⟩ := h
  obtain ⟨hR₁, -, hPm, -⟩ := readOptionalMark_past hR₀ hm
  have hP₁ := hP₀.trans hPm
  obtain ⟨y, r₂, hs₂⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
  by_cases hc : y.isPunct ":" = true
  · have hyk : y.kind = .punct ":" := by simpa [Token.isPunct] using hc
    have hne : y.kind ≠ .eof := by rw [hyk]; simp
    rw [if_pos hc, Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hs₂ hne)), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_ok] at h
    obtain ⟨ty, s₂, hty, h⟩ := h
    obtain ⟨hR₂, hP₂⟩ := (types_skel _).1 _ _ _ (hR₁.past hs₂ (hR₁.more hs₂ hne)) hty
    rw [Parse.pure_bind] at h
    obtain ⟨z, r₃, hs₃⟩ := hR₂.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₃)] at h
    obtain ⟨_, h⟩ := fail_inv h
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ((hP₁.trans (PastSkel.tok hs₂)).trans hP₂).of_eq (by
      rw [hyk]; cases b <;>
        simp [Param.words, optionalMark, typeAnnotation, identWord, punctWord, TypeExpr.tokens, skel, skelKind])
  · rw [if_neg hc, Parse.pure_bind] at h
    rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
    obtain ⟨_, h⟩ := fail_inv h
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact hP₁.of_eq (by cases b <;> simp [Param.words, optionalMark, typeAnnotation, identWord, punctWord, skel, skelKind])

/-- `parseParam` reads items of a list, which are not optional in an arrow
function. -/
theorem parseParam_item {T : Edition} :
    GivesItem T (fun p : Param => (p.wf && !p.optional) && p.words.all (Word.ok T)) (fun p => p.words.flatten)
      (fun _ _ => true) (Parse.parseParam false) := by
  intro s p s' hR hT h
  obtain ⟨hR', hK, hwf, hok⟩ := parseParam_wf s p s' hR hT h
  obtain ⟨src, h1, h2⟩ := parseParam_skel hR h
  have hno := parseParam_notOptional hR h
  exact ⟨hR', hK, ⟨src, h1, h2⟩, both (by simp [hwf, hno]) hok, fun _ _ => rfl⟩

/-- The parameters of an arrow function, as `parseArrowParams` gives them:
one name, or the list in parentheses, as the first token says. -/
theorem parseArrowParams_gives {T : Edition} {s s' : ParseState} {ps : List Param} {first : Token}
    {r : List Token} (hR : Ready s) (hT : s.target = T) (hs : s.rest = first :: r)
    (h : Parse.parseArrowParams s = .ok ps s') :
    Ready s' ∧ Kept s s' ∧ PastSkel s s' (skel (arrowParams (first.isPunct "(") ps).flatten) ∧
      (arrowParams (first.isPunct "(") ps).flatten.head? = some first.kind ∧
      (first.isPunct "(" || bareParam ps) = true ∧ (∀ p ∈ ps, p.wf = true ∧ (!p.optional) = true) ∧
      WordsOK T (arrowParams (first.isPunct "(") ps) := by
  simp only [Parse.parseArrowParams] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hp : first.isPunct "(" = true
  · have hlk : first.kind = .punct "(" := by simpa [Token.isPunct] using hp
    have hne : first.kind ≠ .eof := by rw [hlk]; simp
    simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    rw [Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_ok] at h
    obtain ⟨items, st, hit, h⟩ := h
    have hR₁ := hR.past hs (hR.more hs hne)
    have hL := list_inv parseParam_item (fun _ _ _ h => by
      simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h; exact h.2.symm) hR₁ hT hit
    rw [Parse.bind_ok] at h; obtain ⟨rp, s₂, hrp, h⟩ := h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hR₂, hK₂, ⟨src, h1, h2, _⟩, hwf, _⟩ := bracketed hs hlk (.inl rfl) hL hrp
    rw [hp]
    have hpar : arrowParams true items.toList = enclose "(" ")" (items.toList.map Param.words) := rfl
    refine ⟨hR₂, (Kept.past _ _ _).trans hK₂, ⟨src, h1, by rw [h2, hpar, enclose_params_flatten, List.cons_append]⟩,
      by rw [hpar, enclose_params_flatten, hlk]; rfl, rfl,
      fun p hp => by simpa using both_left (hwf p hp), ?_⟩
    rw [hpar]
    exact wordsOK_enclose (by decide) (by decide) (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact both_right (hwf p hp))
  · have hp' : first.isPunct "(" = false := by simpa using hp
    simp only [hp', Bool.not_false, ↓reduceIte] at h
    rw [Parse.bind_ok] at h; obtain ⟨name, s₁, hn, h⟩ := h
    have hw := readName_words hR hT hn
    obtain ⟨tn, r₁, htk, hnr, hs₀, rfl, hR₁⟩ := readName_inv hR hn
    rw [hs] at hs₀
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs₀
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    rw [hp']
    have hpar : arrowParams false [{ span := first.span, name := name, type := none }] = [identWord name] := rfl
    refine ⟨hR₁, Kept.past _ _ _, (PastSkel.tok hs).of_eq ?_, ?_, rfl, ?_, ?_⟩
    · rw [hpar, htk]; rfl
    · rw [hpar, htk]; rfl
    · intro p hp; simp at hp; subst hp; simpa [Param.wf, exprName] using hnr
    · rw [hpar]; exact WordsOK.word hw

/-- What `parseArrow` gives, when `parseAssign` gives its body. -/
theorem parseArrow_gives {T : Edition} {f : Nat} (hA : GivesE T .assign (Parse.parseAssign f)) :
    GivesE T .assign (Parse.parseArrow (f + 1)) := by
  intro s e s' hR hT h
  obtain ⟨first, r, hs⟩ := hR.cons
  simp only [Parse.parseArrow] at h
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_ok] at h
  obtain ⟨ps, s₁, hpp, h⟩ := h
  obtain ⟨hR₁, hK₁, ⟨psrc, hp1, hp2⟩, hhead, hshape, hpw, hpok⟩ := parseArrowParams_gives hR hT hs hpp
  obtain ⟨y, r₁, hs₁⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
  obtain ⟨_, h⟩ := fail_inv h
  obtain ⟨_, h⟩ := fail_inv h
  rw [Parse.bind_ok] at h; obtain ⟨ar, s₂, har, h⟩ := h
  obtain ⟨hark, r₂, hs₁', rfl, hR₂⟩ := expectPunct_inv hR₁ har
  obtain ⟨_, h⟩ := fail_inv h
  obtain ⟨u, r₃, hs₂⟩ := hR₂.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
  obtain ⟨hnu, h⟩ := fail_inv h
  rw [Parse.bind_ok] at h; obtain ⟨body, s₃, hb, h⟩ := h
  have hT₂ : (past s₁ ar r₂).target = T := hK₁.target_eq.trans hT
  have gb := hA _ _ _ hR₂ hT₂ hb
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨bsrc, hb1, hb2, hb3⟩ := gb.tokens
  have hst : s.rest = psrc ++ ar :: (bsrc ++ s₃.rest) := by rw [hp1, hs₁', ← hb1]
  -- The body does not start with `{`.
  have hbrace : notFirst (.punct "{") body.tokens = true := by
    obtain ⟨k, hk, _⟩ := Expr.first body
    rw [hk] at hb3
    cases bsrc with
    | nil => simp at hb3
    | cons b0 bs =>
      simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hb3
      have e := hs₂.symm.trans hb1
      simp only [List.cons_append, List.cons.injEq] at e
      have hu : b0.kind ≠ .punct "{" := by
        rw [← e.1]; exact fun e' => hnu (by simp [Token.isPunct, e'])
      simp [notFirst, hk, ← hb3, hu]
  refine ⟨gb.ready, hK₁.trans ((Kept.past _ _ _).trans gb.kept), ⟨psrc ++ ar :: bsrc, by rw [hst]; simp, ?_, ?_⟩,
    ?_, fun after hf => by simpa [Expr.afterOK] using gb.after after hf, ?_⟩
  · rw [Expr.tokens_arrow]
    simp only [List.map_append, List.map_cons, skel_append, hp2, hark, skel_nonSkel (k := .punct "=>") rfl, hb2]
  · rw [Expr.tokens_arrow]
    have hne : (arrowParams (first.isPunct "(") ps).flatten ≠ [] := by intro h'; rw [h'] at hhead; simp at hhead
    have hfirst : (psrc.map (·.kind) ++ (ar :: bsrc).map (·.kind)).head? = some first.kind := by
      have := congrArg (fun l : List Token => (l.map (·.kind)).head?) hst
      simp only [hs, List.map_cons, List.head?_cons, List.map_append] at this
      rw [this]; simp
    simp only [List.map_append] at hfirst ⊢
    rw [hfirst]
    cases hf : (arrowParams (first.isPunct "(") ps).flatten with
    | nil => exact absurd hf hne
    | cons k ks => rw [hf] at hhead; simpa using hhead.symm
  · simp only [Expr.wfAt, Bool.and_eq_true, List.all_eq_true]
    exact ⟨⟨⟨hshape, hpw⟩, gb.wf⟩, hbrace⟩
  · simpa [Expr.words] using hpok.append (WordsOK.cons (ok_punct (by decide)) gb.ok)

/-- Every function of the expression parser gives what `GaveE` states, at its
level, for every amount of fuel. -/
theorem exprs_give (T : Edition) : ∀ f : Nat,
    GivesE T .assign (Parse.parseExpression f) ∧ GivesE T .assign (Parse.parseAssign f) ∧
    GivesE T .cond (Parse.parseConditional f) ∧ (∀ m, GivesBin T m (Parse.parseBinary f m)) ∧
    GivesE T .unary (Parse.parseUnary f) ∧ GivesE T .postfix (Parse.parsePostfix f) ∧
    GivesE T .lhs (Parse.parseLeftHandSide f) ∧ GivesArgs T (Parse.parseArguments f) ∧
    GivesE T .primary (Parse.parseArrayLiteral f) ∧
    GivesItem T (fun q => Property.wf T q && q.words.all (Word.ok T)) Property.tokens (fun after q => q.afterOK after)
      (Parse.parseProperty f) ∧
    GivesE T .primary (Parse.parseObjectLiteral f) ∧ GivesE T .primary (Parse.parsePrimary f) ∧
    GivesE T .assign (Parse.parseArrow f) ∧ GivesNew T (Parse.parseNew f)
  | 0 => by
    refine ⟨?_, ?_, ?_, fun m => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro s e s' _ _ h <;>
      first
      | (simp only [Parse.parseNew] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parseArrow] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parseExpression] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parseAssign] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parseConditional] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parseBinary] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parseUnary] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parsePostfix] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parseLeftHandSide] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parseArguments] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parseArrayLiteral] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parseProperty] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parseObjectLiteral] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
      | (simp only [Parse.parsePrimary] at h; exact absurd h (outOfFuel_ne_ok _ _ _))
  | f + 1 => by
    obtain ⟨hE, hA, hC, hB, hU, hP, hL, hArgs, hArr, hProp, hObj, hPrim, hW, hNew⟩ := exprs_give T f
    exact ⟨parseExpression_gives hA, parseAssign_gives hA hC hW, parseConditional_gives hA (hB 0),
      fun m => parseBinary_gives hB hU, parseUnary_gives hU hL hP, parsePostfix_gives hL,
      parseLeftHandSide_gives hE hArgs hPrim, parseArguments_gives hA, parseArrayLiteral_gives hA,
      parseProperty_gives hA, parseObjectLiteral_gives hProp, parsePrimary_gives hE hArr hObj hNew,
      parseArrow_gives hA, parseNew_gives hArgs⟩

/-! ### Statements -/

theorem VarKind.word_ok (T : Edition) : ∀ k : VarKind, Word.ok T k.word = true
  | .const => by simp only [VarKind.word]; word_ok
  | .«let» => by simp only [VarKind.word]; word_ok

theorem exportWords_ok (T : Edition) (e : Bool) : WordsOK T (exportWords e) := by
  cases e <;> simp only [exportWords, Bool.false_eq_true, ↓reduceIte] <;> words_ok

theorem VarDecl.wordsOK {T : Edition} (d : VarDecl) (hn : Word.ok T (identWord d.name) = true)
    (ht : ∀ t, d.type = some t → WordsOK T t.words) (he : ∀ e, d.init = some e → WordsOK T e.words) :
    WordsOK T d.words := by
  have hk := VarKind.word_ok T d.kind
  have h1 := typeAnnotation_ok ht
  have h2 : WordsOK T (match d.init with | some e => punctWord "=" :: e.words | none => []) := by
    cases h : d.init with
    | none => exact WordsOK.nil
    | some e => have := he e h; words_ok
  unfold VarDecl.words
  words_ok

theorem Field.wordsOK {T : Edition} (f : Field) (hn : Word.ok T (propertyName f.name) = true)
    (ht : WordsOK T f.type.words) : WordsOK T f.words := by
  unfold Field.words
  split <;> split <;> words_ok

theorem EnumMember.wordsOK {T : Edition} (m : EnumMember) (hn : Word.ok T (propertyName m.name) = true)
    (hv : Word.ok T [.string m.value] = true) : WordsOK T m.words := by
  unfold EnumMember.words
  words_ok

theorem ImportName.wordsOK {T : Edition} (n : ImportName) (hn : Word.ok T (identWord n.name) = true) :
    WordsOK T n.words := by
  unfold ImportName.words
  split <;> words_ok

/-- Every line that `st` prints, at every depth, has words that lex back. -/
def StmtOK (T : Edition) (st : Stmt) : Prop := ∀ d, ∀ l ∈ st.lines d, WordsOK T l.2

theorem StmtOK.one {T : Edition} {st : Stmt} {ws : List Word} (h : ∀ d, st.lines d = [(d, ws)])
    (hw : WordsOK T ws) : StmtOK T st := by
  intro d l hl; rw [h d, List.mem_singleton] at hl; subst hl; exact hw

theorem StmtOK.head {T : Edition} {st b : Stmt} {ws : List Word} (h : ∀ d, st.lines d = (d, ws) :: b.lines (d + 1))
    (hw : WordsOK T ws) (hb : StmtOK T b) : StmtOK T st := by
  intro d l hl; rw [h d] at hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact hw
  · exact hb _ l hl

section
variable {T : Edition} {sp : Span}

theorem StmtOK.varDecl {d : VarDecl} (hd : WordsOK T d.words) : StmtOK T (.varDecl sp d) :=
  StmtOK.one (fun _ => rfl) hd

theorem StmtOK.exprStmt {e : Expr} (he : WordsOK T e.words) : StmtOK T (.exprStmt sp e) :=
  StmtOK.one (fun _ => rfl) (by words_ok)

theorem StmtOK.retNone : StmtOK T (.returnStmt sp none) := StmtOK.one (fun _ => rfl) (by words_ok)

theorem StmtOK.retSome {e : Expr} (he : WordsOK T e.words) : StmtOK T (.returnStmt sp (some e)) :=
  StmtOK.one (fun _ => rfl) (by words_ok)

theorem StmtOK.throw {e : Expr} (he : WordsOK T e.words) : StmtOK T (.throwStmt sp e) :=
  StmtOK.one (fun _ => rfl) (by words_ok)

theorem StmtOK.brk : StmtOK T (.breakStmt sp) := StmtOK.one (fun _ => rfl) (by words_ok)

theorem StmtOK.cont : StmtOK T (.continueStmt sp) := StmtOK.one (fun _ => rfl) (by words_ok)

theorem StmtOK.empty : StmtOK T (.empty sp) := StmtOK.one (fun _ => rfl) (by words_ok)

theorem StmtOK.ifThen {test : Expr} {t : Stmt} (h1 : WordsOK T test.words) (ht : StmtOK T t) :
    StmtOK T (.ifStmt sp test t none) :=
  StmtOK.head (fun _ => rfl) (by words_ok) ht

theorem StmtOK.ifElse {test : Expr} {t e : Stmt} (h1 : WordsOK T test.words) (ht : StmtOK T t) (he : StmtOK T e) :
    StmtOK T (.ifStmt sp test t (some e)) := by
  intro d l hl
  simp only [Stmt.lines, List.mem_cons, List.mem_append] at hl
  rcases hl with (rfl | hl) | (rfl | hl)
  · words_ok
  · exact ht _ l hl
  · words_ok
  · exact he _ l hl

theorem StmtOK.forOf {kind : VarKind} {name : String} {it : Expr} {body : Stmt} (h1 : WordsOK T it.words)
    (hn : Word.ok T (identWord name) = true) (hb : StmtOK T body) : StmtOK T (.forOfStmt sp kind name it body) := by
  have hk := VarKind.word_ok T kind
  exact StmtOK.head (fun _ => rfl) (by words_ok) hb

theorem StmtOK.counted {init : Option VarDecl} {test update : Option Expr} {body : Stmt}
    (hi : ∀ d, init = some d → WordsOK T d.words) (ht : ∀ e, test = some e → WordsOK T e.words)
    (hu : ∀ e, update = some e → WordsOK T e.words) (hb : StmtOK T body) :
    StmtOK T (.forStmt sp init test update body) := by
  have h1 : WordsOK T (forInitWords init) := by
    cases init with
    | none => simp only [forInitWords]; words_ok
    | some d => exact hi d rfl
  have h2 : WordsOK T (optWords test) := by
    cases test with
    | none => exact WordsOK.nil
    | some e => exact ht e rfl
  have h3 : WordsOK T (optWords update) := by
    cases update with
    | none => exact WordsOK.nil
    | some e => exact hu e rfl
  exact StmtOK.head (fun _ => rfl) (by words_ok) hb

theorem StmtOK.while {test : Expr} {body : Stmt} (h1 : WordsOK T test.words) (hb : StmtOK T body) :
    StmtOK T (.whileStmt sp test body) :=
  StmtOK.head (fun _ => rfl) (by words_ok) hb

theorem linesOf_ok : ∀ ss : List Stmt, (∀ x ∈ ss, StmtOK T x) → ∀ d, ∀ l ∈ Stmt.linesOf d ss, WordsOK T l.2
  | [], _, d, l, hl => by simp [Stmt.linesOf] at hl
  | x :: ss, h, d, l, hl => by
    simp only [Stmt.linesOf, List.mem_append] at hl
    rcases hl with hl | hl
    · exact h x (by simp) d l hl
    · exact linesOf_ok ss (fun y hy => h y (by simp [hy])) d l hl

theorem StmtOK.block {body : List Stmt} (h : ∀ x ∈ body, StmtOK T x) : StmtOK T (.block sp body) := by
  intro d l hl
  simp only [Stmt.lines, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | hl) | rfl
  · words_ok
  · exact linesOf_ok body h _ l hl
  · words_ok

/-- The words of every line of a clause of a `switch` lex back. -/
def ClauseOK (T : Edition) (c : Option Expr × List Stmt) : Prop :=
  WordsOK T (clauseHead c.1) ∧ ∀ x ∈ c.2, StmtOK T x

theorem clauseLines_ok : ∀ cs : List (Option Expr × List Stmt), (∀ c ∈ cs, ClauseOK T c) →
    ∀ d, ∀ l ∈ Stmt.clauseLines d cs, WordsOK T l.2
  | [], _, d, l, hl => by simp [Stmt.clauseLines] at hl
  | (t, b) :: cs, h, d, l, hl => by
    simp only [Stmt.clauseLines, List.mem_cons, List.mem_append] at hl
    rcases hl with (rfl | hl) | hl
    · exact (h (t, b) (by simp)).1
    · exact linesOf_ok b (h (t, b) (by simp)).2 (d + 1) l hl
    · exact clauseLines_ok cs (fun c hc => h c (by simp [hc])) d l hl

theorem StmtOK.switch {disc : Expr} {cs : List (Option Expr × List Stmt)} (h1 : WordsOK T disc.words)
    (hc : ∀ c ∈ cs, ClauseOK T c) : StmtOK T (.switchStmt sp disc cs) := by
  intro d l hl
  simp only [Stmt.lines, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | hl) | rfl
  · words_ok
  · exact clauseLines_ok cs hc _ l hl
  · words_ok

end

theorem endStatement_inv {s s' : ParseState} (hR : Ready s) (h : Parse.endStatement s = .ok () s') :
    Ready s' ∧ Kept s s' := by
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.endStatement] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases h1 : x.isPunct ";" = true
  · have hk : x.kind = .punct ";" := by simpa [Token.isPunct] using h1
    have hne : x.kind ≠ .eof := by rw [hk]; simp
    rw [if_pos h1, Parse.discard_eq (advance_past hR hs hne)] at h
    cases h
    exact ⟨hR.past hs (hR.more hs hne), Kept.past _ _ _⟩
  · rw [if_neg h1] at h
    split at h
    · simp only [Parse.pure_ok] at h; obtain ⟨_, rfl⟩ := h; exact ⟨hR, Kept.refl _⟩
    · exact absurd h (Parse.unexpected_ne_ok _ _ _ _ _)

/-- The end of `parseDeclaration`: no second variable, and a `const` has a
value. -/
theorem varDecl_tail {β : Type} {st s' : ParseState} {c : Prop} [Decidable c] {kw : Token} {d d' : β}
    (hR : Ready st)
    (h : (Parse.peek >>= fun t =>
      if t.isPunct "," = true then (Parse.failAt (A := PUnit) t "declare one variable per statement" >>= fun _ =>
        if c then Parse.failAt (A := PUnit) kw "a 'const' needs a value" >>= fun _ => pure d
        else pure PUnit.unit >>= fun _ => pure d)
      else (pure PUnit.unit >>= fun _ =>
        if c then Parse.failAt (A := PUnit) kw "a 'const' needs a value" >>= fun _ => pure d
        else pure PUnit.unit >>= fun _ => pure d)) st = .ok d' s') :
    ¬c ∧ d' = d ∧ Ready s' ∧ Kept st s' := by
  obtain ⟨t, r, hs⟩ := hR.cons
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  obtain ⟨_, h⟩ := fail_inv h
  obtain ⟨hc, h⟩ := fail_inv h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨hc, rfl, hR, Kept.refl _⟩

theorem parseDeclaration_inv {T : Edition} {s s' : ParseState} {d : VarDecl} {x : Token} {r : List Token}
    (hR : Ready s) (hT : s.target = T) (hs : s.rest = x :: r) (hx : x.kind ≠ .eof)
    (h : Parse.parseDeclaration s = .ok d s') : Ready s' ∧ Kept s s' ∧ d.wf T = true ∧ WordsOK T d.words := by
  simp only [Parse.parseDeclaration] at h
  rw [Parse.bind_eq (advance_past hR hs hx)] at h
  have hR₁ := hR.past hs (hR.more hs hx)
  obtain ⟨y, r₁, hs₁⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
  obtain ⟨_, h⟩ := fail_inv h
  rw [Parse.bind_ok] at h; obtain ⟨name, s₂, hn, h⟩ := h
  have hnok := readName_words hR₁ hT hn
  obtain ⟨tn, r₂, _, hnr, _, rfl, hR₂⟩ := readName_inv hR₁ hn
  have hname : exprName name = true := by simpa [exprName] using hnr
  have hT₂ : (past (past s x r) tn r₂).target = T := hT
  obtain ⟨z, r₃, hs₃⟩ := hR₂.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₃)] at h
  have hK₂ : Kept s (past (past s x r) tn r₂) := (Kept.past _ _ _).trans (Kept.past _ _ _)
  by_cases hcol : z.isPunct ":" = true
  · have hzk : z.kind = .punct ":" := by simpa [Token.isPunct] using hcol
    have hzne : z.kind ≠ .eof := by rw [hzk]; simp
    have hR₃' := hR₂.past hs₃ (hR₂.more hs₃ hzne)
    rw [if_pos hcol, Parse.bind_eq (Parse.discard_eq (advance_past hR₂ hs₃ hzne)), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_ok] at h
    obtain ⟨ty, s₃, hty, h⟩ := h
    obtain ⟨htwo, hR₃, hK₃⟩ := (types_give T _).1 _ _ _ hR₃' hT hty
    have htw := both_left htwo
    have htok := both_right htwo
    rw [Parse.pure_bind] at h
    have hK₃' : Kept s s₃ := hK₂.trans ((Kept.past _ _ _).trans hK₃)
    obtain ⟨w, r₄, hs₄⟩ := hR₃.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₄)] at h
    by_cases heq : w.isPunct "=" = true
    · have hwk : w.kind = .punct "=" := by simpa [Token.isPunct] using heq
      have hwne : w.kind ≠ .eof := by rw [hwk]; simp
      have hR₄ := hR₃.past hs₄ (hR₃.more hs₄ hwne)
      rw [if_pos heq, Parse.bind_eq (Parse.discard_eq (advance_past hR₃ hs₄ hwne)), Parse.bind_eq (Parse.budget_eq _),
        Parse.bind_ok] at h
      obtain ⟨v, s₅, hv, h⟩ := h
      have gv := (exprs_give T _).2.1 _ _ _ hR₄ (by rw [show (past s₃ w r₄).target = s₃.target from rfl,
        hK₃'.target_eq, hT]) hv
      rw [Parse.pure_bind] at h
      obtain ⟨_, rfl, hR', hK'⟩ := varDecl_tail gv.ready h
      refine ⟨hR', hK₃'.trans ((Kept.past _ _ _).trans (gv.kept.trans hK')), ?_,
        VarDecl.wordsOK _ hnok (fun t ht => by simp at ht; subst ht; exact htok)
          (fun e he => by simp at he; subst he; exact gv.ok)⟩
      simp only [VarDecl.wf, Bool.and_eq_true]
      exact ⟨⟨hname, htw⟩, gv.wf, gv.after _ (follows_end (.inl rfl))⟩
    · rw [if_neg heq, Parse.pure_bind] at h
      obtain ⟨hc, rfl, hR', hK'⟩ := varDecl_tail hR₃ h
      refine ⟨hR', hK₃'.trans hK', ?_,
        VarDecl.wordsOK _ hnok (fun t ht => by simp at ht; subst ht; exact htok) (fun e he => by simp at he)⟩
      simp only [VarDecl.wf, Bool.and_eq_true]
      refine ⟨⟨hname, htw⟩, ?_⟩
      revert hc; cases x.isKeyword "const" <;> decide
  · rw [if_neg hcol, Parse.pure_bind] at h
    obtain ⟨w, r₄, hs₄⟩ := hR₂.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₄)] at h
    by_cases heq : w.isPunct "=" = true
    · have hwk : w.kind = .punct "=" := by simpa [Token.isPunct] using heq
      have hwne : w.kind ≠ .eof := by rw [hwk]; simp
      have hR₄ := hR₂.past hs₄ (hR₂.more hs₄ hwne)
      rw [if_pos heq, Parse.bind_eq (Parse.discard_eq (advance_past hR₂ hs₄ hwne)), Parse.bind_eq (Parse.budget_eq _),
        Parse.bind_ok] at h
      obtain ⟨v, s₅, hv, h⟩ := h
      have gv := (exprs_give T _).2.1 _ _ _ hR₄ hT₂ hv
      rw [Parse.pure_bind] at h
      obtain ⟨_, rfl, hR', hK'⟩ := varDecl_tail gv.ready h
      refine ⟨hR', hK₂.trans ((Kept.past _ _ _).trans (gv.kept.trans hK')), ?_,
        VarDecl.wordsOK _ hnok (fun t ht => by simp at ht) (fun e he => by simp at he; subst he; exact gv.ok)⟩
      simp only [VarDecl.wf, Bool.and_eq_true]
      exact ⟨⟨hname, trivial⟩, gv.wf, gv.after _ (follows_end (.inl rfl))⟩
    · rw [if_neg heq, Parse.pure_bind] at h
      obtain ⟨hc, rfl, hR', hK'⟩ := varDecl_tail hR₂ h
      refine ⟨hR', hK₂.trans hK', ?_,
        VarDecl.wordsOK _ hnok (fun t ht => by simp at ht) (fun e he => by simp at he)⟩
      simp only [VarDecl.wf, Bool.and_eq_true]
      refine ⟨⟨hname, trivial⟩, ?_⟩
      revert hc; cases x.isKeyword "const" <;> decide

theorem parseVarDecl_inv {T : Edition} {s s' : ParseState} {d : VarDecl} {x : Token} {r : List Token}
    (hR : Ready s) (hT : s.target = T) (hs : s.rest = x :: r) (hx : x.kind ≠ .eof)
    (h : Parse.parseVarDecl s = .ok d s') : Ready s' ∧ Kept s s' ∧ d.wf T = true ∧ WordsOK T d.words := by
  simp only [Parse.parseVarDecl] at h
  rw [Parse.bind_ok] at h; obtain ⟨d₁, s₁, hd, h⟩ := h
  obtain ⟨hR₁, hK₁, hw, hok⟩ := parseDeclaration_inv hR hT hs hx hd
  rw [Parse.bind_ok] at h; obtain ⟨_, s₂, he, h⟩ := h
  obtain ⟨hR₂, hK₂⟩ := endStatement_inv hR₁ he
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨hR₂, hK₁.trans hK₂, hw, hok⟩

/-- What a function of the statement parser gives: a statement that `Stmt.wf`
accepts in the state's function and loop. A statement that ends with an `if`
without `else` has no `else` after it, and a declaration starts with `const`
or `let`. -/
def GivesS (T : Edition) (p : ParseM Stmt) : Prop :=
  ∀ s st s', Ready s → s.target = T → p s = .ok st s' →
    Ready s' ∧ Kept s s' ∧ st.wf T s.inFunction (s.loopDepth != 0) = true ∧
      (st.openIf = true → ∀ u ∈ s'.rest.head?, u.kind ≠ .keyword "else") ∧
      (st.isDecl = true → ∀ x ∈ s.rest.head?, x.kind = .keyword "const" ∨ x.kind = .ident "let") ∧
      StmtOK T st

theorem blockStep_inv {T : Edition} {p : ParseM Stmt} (hp : GivesS T p) {s₀ : ParseState} {items items' : Array Stmt}
    {b : Bool} {st st' : ParseState} (hT : s₀.target = T)
    (hI : Ready st ∧ Kept s₀ st ∧
      ∀ x ∈ items.toList, x.wf T s₀.inFunction (s₀.loopDepth != 0) = true ∧ StmtOK T x)
    (h : Parse.blockStep p items st = .ok (items', b) st') :
    Ready st' ∧ Kept s₀ st' ∧ ∀ x ∈ items'.toList, x.wf T s₀.inFunction (s₀.loopDepth != 0) = true ∧ StmtOK T x := by
  obtain ⟨hR, hK, hall⟩ := hI
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.blockStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : x.isPunct "}" = true
  · rw [if_pos hc] at h; simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR, hK, hall⟩
  rw [if_neg hc, Parse.pure_bind] at h
  by_cases he : x.isEof = true
  · rw [if_pos he] at h; exact absurd h (unexpected_bind_ne_ok _ _ _ _ _ _)
  rw [if_neg he, Parse.pure_bind, Parse.bind_ok] at h
  obtain ⟨y, s₁, hy, h⟩ := h
  obtain ⟨hR₁, hK₁, hw, _, _, hok⟩ := hp _ _ _ hR (hK.target_eq.trans hT) hy
  simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
  refine ⟨hR₁, hK.trans hK₁, fun x' hx' => ?_⟩
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx'
  rcases hx' with hx' | rfl
  · exact hall x' hx'
  · exact ⟨by rw [← hK.inFunction_eq, ← hK.loopDepth_eq]; exact hw, hok⟩

theorem parseBlock_gives {T : Edition} {f : Nat} (hS : GivesS T (Parse.parseStatement f)) :
    GivesS T (Parse.parseBlock (f + 1)) := by
  intro s st s' hR hT h
  simp only [Parse.parseBlock] at h
  rw [Parse.bind_ok] at h; obtain ⟨lb, s₁, hl, h⟩ := h
  obtain ⟨hlk, r, hs, rfl, hR₁⟩ := expectPunct_inv hR hl
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h; obtain ⟨items, s₂, hit, h⟩ := h
  obtain ⟨hR₂, hK₂, hall⟩ := (iterate_inv
    (I := fun a st => Ready st ∧ Kept (past s lb r) st ∧
      ∀ x ∈ a.toList, x.wf T (past s lb r).inFunction ((past s lb r).loopDepth != 0) = true ∧ StmtOK T x)
    (fun _ _ _ _ _ hI hst => blockStep_inv (s₀ := past s lb r) hS (show (past s lb r).target = T from hT) hI hst)
    _ #[] _ items s₂ ⟨hR₁, Kept.refl _, by simp⟩ hit).1
  rw [Parse.bind_ok] at h; obtain ⟨rb, s₃, hrb, h⟩ := h
  obtain ⟨_, r₃, _, rfl, hR₃⟩ := expectPunct_inv hR₂ hrb
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  refine ⟨hR₃, (Kept.past _ _ _).trans (hK₂.trans (Kept.past _ _ _)), ?_, by simp [Stmt.openIf],
    by simp [Stmt.isDecl], StmtOK.block (fun x hx => (hall x hx).2)⟩
  simpa [Stmt.wf] using Stmt.allWF_iff.mpr (fun x hx => (hall x hx).1)

/-- A branch: a statement that is not a declaration. -/
def GivesB (T : Edition) (p : ParseM Stmt) : Prop :=
  ∀ s st s', Ready s → s.target = T → p s = .ok st s' →
    Ready s' ∧ Kept s s' ∧ st.wf T s.inFunction (s.loopDepth != 0) = true ∧
      (st.openIf = true → ∀ u ∈ s'.rest.head?, u.kind ≠ .keyword "else") ∧ st.isDecl = false ∧ StmtOK T st

theorem parseBranch_gives {T : Edition} {f : Nat} (hS : GivesS T (Parse.parseStatement f)) :
    GivesB T (Parse.parseBranch (f + 1)) := by
  intro s st s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseBranch] at h
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_ok] at h
  obtain ⟨_, s₁, hd, h⟩ := h
  simp only [Parse.refuseDeclaration] at hd
  by_cases hc : (x.isKeyword "const" || x.isIdent "let") = true
  · rw [if_pos hc] at hd; exact absurd hd (Parse.failAt_ne_ok _ _ _ _ _)
  rw [if_neg hc] at hd; simp only [Parse.pure_ok] at hd; obtain ⟨_, rfl⟩ := hd
  obtain ⟨hR', hK', hw, ho, hdecl, hok⟩ := hS _ _ _ hR hT h
  refine ⟨hR', hK', hw, ho, ?_, hok⟩
  cases hst : st.isDecl
  · rfl
  · exfalso
    rcases hdecl hst x (by simp [hs]) with h' | h' <;> simp [Token.isKeyword, Token.isIdent, h'] at hc

/-- `withLoop` reads its body in a loop and leaves the loop depth as it was. -/
theorem withLoop_inv {T : Edition} {p : ParseM Stmt} (hp : GivesB T p) {s s' : ParseState} {st : Stmt} (hR : Ready s)
    (hT : s.target = T) (h : Parse.withLoop p s = .ok st s') :
    Ready s' ∧ Kept s s' ∧ st.wf T s.inFunction true = true ∧
      (st.openIf = true → ∀ u ∈ s'.rest.head?, u.kind ≠ .keyword "else") ∧ st.isDecl = false ∧ StmtOK T st := by
  simp only [Parse.withLoop] at h
  rw [Parse.bind_eq (Parse.modify_eq _ s), Parse.bind_ok] at h
  obtain ⟨b, s₂, hb, h⟩ := h
  have hR₁ : Ready { s with loopDepth := s.loopDepth + 1 } := ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2⟩
  obtain ⟨hR₂, hK₂, hw, ho, hd, hok⟩ := hp _ _ _ hR₁ hT hb
  rw [Parse.bind_eq (Parse.modify_eq _ s₂)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  refine ⟨⟨hR₂.1, hR₂.2.1, hR₂.2.2.1, hR₂.2.2.2⟩, ⟨hK₂.eof_eq, hK₂.inFunction_eq, ?_, hK₂.target_eq⟩, ?_, ho, hd,
    hok⟩
  · simp [hK₂.loopDepth_eq]
  · simpa using hw

/-- An expression statement: an expression that starts with the first token, then the end of the statement. -/
theorem parseExpressionStatement_inv {T : Edition} {f : Nat} {s s' : ParseState} {st : Stmt} {x : Token}
    {r : List Token} (hR : Ready s) (hT : s.target = T) (hs : s.rest = x :: r)
    (h : Parse.parseExpressionStatement (f + 1) s = .ok st s') :
    Ready s' ∧ Kept s s' ∧ ∃ sp e, st = .exprStmt sp e ∧ e.wfAt T .assign = true ∧
      e.afterOK [.punct ";"] = true ∧ e.tokens.head? = some x.kind ∧ WordsOK T e.words := by
  simp only [Parse.parseExpressionStatement] at h
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
  obtain ⟨e, s₁, he, h⟩ := h
  have ge := (exprs_give T _).1 _ _ _ hR hT he
  rw [Parse.bind_ok] at h; obtain ⟨_, s₂, hend, h⟩ := h
  obtain ⟨hR₂, hK₂⟩ := endStatement_inv ge.ready hend
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨src, h1, _, h3⟩ := ge.tokens
  refine ⟨hR₂, ge.kept.trans hK₂, _, e, rfl, ge.wf, ge.after _ (follows_end (.inl rfl)), ?_, ge.ok⟩
  rw [← h3]
  cases src with
  | nil => obtain ⟨k, hk, _⟩ := Expr.first e; rw [← h3] at hk; simp at hk
  | cons y src => rw [hs] at h1; simp at h1; simp [h1.1]

/-- `unless c do failAt …`, where the parser went on: `c` holds. -/
theorem pass_inv {β : Type} {c : Prop} [Decidable c] {t : Token} {msg : String} {K : PUnit → ParseM β}
    {s s' : ParseState} {r : β} (h : (if c then pure PUnit.unit >>= K else Parse.failAt t msg >>= K) s = .ok r s') :
    c ∧ K () s = .ok r s' := by
  by_cases hc : c
  · rw [if_pos hc, Parse.pure_bind] at h; exact ⟨hc, h⟩
  · rw [if_neg hc] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)

/-- A value that one of two tests picks, or a refusal. -/
theorem choose_inv {α β : Type} {c1 c2 : Prop} [Decidable c1] [Decidable c2] {a b : α} {t : Token} {msg : String}
    {K : α → ParseM β} {s s' : ParseState} {r : β}
    (h : (if c1 then pure a >>= K else if c2 then pure b >>= K else Parse.failAt t msg >>= K) s = .ok r s') :
    (c1 ∨ c2) ∧ ∃ k, K k s = .ok r s' := by
  by_cases h1 : c1
  · rw [if_pos h1, Parse.pure_bind] at h; exact ⟨.inl h1, a, h⟩
  · rw [if_neg h1] at h
    by_cases h2 : c2
    · rw [if_pos h2, Parse.pure_bind] at h; exact ⟨.inr h2, b, h⟩
    · rw [if_neg h2] at h; exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)

theorem parseForOf_inv {T : Edition} {f : Nat} (hB : GivesB T (Parse.parseBranch f)) {s s' : ParseState} {st : Stmt}
    {x : Token} {r : List Token} (hR : Ready s) (hT : s.target = T) (hs : s.rest = x :: r) (hx : x.kind ≠ .eof)
    (h : Parse.parseForOf (f + 1) s = .ok st s') :
    Ready s' ∧ Kept s s' ∧ st.wf T s.inFunction (s.loopDepth != 0) = true ∧
      (st.openIf = true → ∀ u ∈ s'.rest.head?, u.kind ≠ .keyword "else") ∧ st.isDecl = false ∧ StmtOK T st := by
  simp only [Parse.parseForOf] at h
  rw [Parse.bind_eq (advance_past hR hs hx)] at h
  have hR₁ := hR.past hs (hR.more hs hx)
  obtain ⟨y, r₁, hs₁⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
  obtain ⟨_, h⟩ := fail_inv h
  rw [Parse.bind_ok] at h; obtain ⟨lp, s₂, hlp, h⟩ := h
  obtain ⟨_, r₂, _, rfl, hR₂⟩ := expectPunct_inv hR₁ hlp
  obtain ⟨kw, r₃, hs₃⟩ := hR₂.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₃)] at h
  obtain ⟨hkc, kind, h⟩ := choose_inv h
  have hkne : kw.kind ≠ .eof := by
    rcases hkc with h1 | h1
    · simp [Token.isKeyword] at h1; rw [h1]; simp
    · simp [Token.isIdent] at h1; rw [h1]; simp
  have hR₃ := hR₂.past hs₃ (hR₂.more hs₃ hkne)
  rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₂ hs₃ hkne))] at h
  obtain ⟨z, r₄, hs₄⟩ := hR₃.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₄)] at h
  obtain ⟨_, h⟩ := fail_inv h
  rw [Parse.bind_ok] at h; obtain ⟨name, s₄, hn, h⟩ := h
  have hnok := readName_words hR₃ hT hn
  obtain ⟨tn, r₅, _, hnr, _, rfl, hR₄⟩ := readName_inv hR₃ hn
  obtain ⟨o, r₆, hs₆⟩ := hR₄.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₆)] at h
  obtain ⟨hof, h⟩ := pass_inv h
  have hone : o.kind ≠ .eof := by simp [Token.isIdent] at hof; rw [hof]; simp
  have hR₅ := hR₄.past hs₆ (hR₄.more hs₆ hone)
  rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₄ hs₆ hone)), Parse.bind_eq (Parse.budget_eq _),
    Parse.bind_ok] at h
  obtain ⟨it, s₅, hit, h⟩ := h
  have git := (exprs_give T _).2.1 _ _ _ hR₅ hT hit
  rw [Parse.bind_ok] at h; obtain ⟨rp, s₆, hrp, h⟩ := h
  obtain ⟨_, r₇, _, rfl, hR₆⟩ := expectPunct_inv git.ready hrp
  rw [Parse.bind_ok] at h; obtain ⟨body, s₇, hbody, h⟩ := h
  have hT₆ : (past s₅ rp r₇).target = T := by
    rw [show (past s₅ rp r₇).target = s₅.target from rfl, git.kept.target_eq]; exact hT
  obtain ⟨hR₇, hK₇, hbw, hbo, hbd, hbok⟩ := withLoop_inv hB hR₆ hT₆ hbody
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  have hK : Kept s (past s₅ rp r₇) :=
    (Kept.past _ _ _).trans ((Kept.past _ _ _).trans ((Kept.past _ _ _).trans ((Kept.past _ _ _).trans
      ((Kept.past _ _ _).trans (git.kept.trans (Kept.past _ _ _))))))
  refine ⟨hR₇, hK.trans hK₇, ?_, by simpa [Stmt.openIf] using hbo, by simp [Stmt.isDecl],
    StmtOK.forOf git.ok hnok hbok⟩
  simp only [Stmt.wf, Bool.and_eq_true, Bool.not_eq_true', Expr.wfParen]
  refine ⟨⟨⟨by simpa [exprName] using hnr, git.wf, git.after _ (follows_end (.inr rfl))⟩, hbd⟩, ?_⟩
  rw [← hK.inFunction_eq]; exact hbw

/-- The declaration at the start of a counted `for`. -/
theorem parseForDeclaration_inv {T : Edition} {s s' : ParseState} {d : VarDecl} (hR : Ready s) (hT : s.target = T)
    (h : Parse.parseForDeclaration s = .ok d s') :
    Ready s' ∧ Kept s s' ∧ d.wf T = true ∧ d.inFree = true ∧ WordsOK T d.words := by
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseForDeclaration] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  obtain ⟨hk, h⟩ := pass_inv h
  have hx : x.kind ≠ .eof := by
    simp only [Bool.or_eq_true, Token.isKeyword, Token.isIdent, beq_iff_eq] at hk
    rcases hk with hk | hk <;> rw [hk] <;> simp
  rw [Parse.bind_ok] at h; obtain ⟨d₁, s₁, hd, h⟩ := h
  obtain ⟨hR₁, hK₁, hw, hok⟩ := parseDeclaration_inv hR hT hs hx hd
  obtain ⟨hi, h⟩ := fail_inv h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨hR₁, hK₁, hw, by simpa using hi, hok⟩

/-- The first part of a counted `for`: nothing, or a declaration. -/
theorem forInit_inv {T : Edition} {s s' : ParseState} {i : Option VarDecl} (hR : Ready s) (hT : s.target = T)
    (h : Parse.unlessPunct ";" Parse.parseForDeclaration s = .ok i s') :
    Ready s' ∧ Kept s s' ∧ VarDecl.forWF T i = true ∧ ∀ d, i = some d → WordsOK T d.words := by
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.unlessPunct] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  split at h
  · simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR, Kept.refl _, rfl, by simp⟩
  · rw [Parse.pure_bind, Parse.bind_ok] at h; obtain ⟨d, s₁, hd, h⟩ := h
    obtain ⟨hR₁, hK₁, hw, hi, hok⟩ := parseForDeclaration_inv hR hT hd
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨hR₁, hK₁, ?_, fun d' hd' => by cases hd'; exact hok⟩
    simp only [VarDecl.forWF, Bool.and_eq_true]; exact ⟨hw, hi⟩

/-- The test or the update of a counted `for`, or nothing, before the `;` or
`)` that `stop` names. -/
theorem forPart_inv {T : Edition} {stop : String} (hstop : stop = ";" ∨ stop = ")") {s s' : ParseState}
    {o : Option Expr} (hR : Ready s) (hT : s.target = T)
    (h : Parse.unlessPunct stop (do Parse.parseExpression (← Parse.budget)) s = .ok o s') :
    Ready s' ∧ Kept s s' ∧ Expr.optWF T stop o = true ∧ ∀ e, o = some e → WordsOK T e.words := by
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.unlessPunct] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  split at h
  · simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR, Kept.refl _, rfl, by simp⟩
  · rw [Parse.pure_bind, Parse.bind_ok] at h; obtain ⟨e, s₁, he, h⟩ := h
    rw [Parse.bind_eq (Parse.budget_eq _)] at he
    have ge := (exprs_give T _).1 _ _ _ hR hT he
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨ge.ready, ge.kept, ?_, fun e' he' => by cases he'; exact ge.ok⟩
    simp only [Expr.optWF, Bool.and_eq_true]; exact ⟨ge.wf, ge.after _ (follows_end hstop)⟩

theorem parseFor_inv {T : Edition} {f : Nat} (hB : GivesB T (Parse.parseBranch f)) {s s' : ParseState} {st : Stmt}
    {x : Token} {r : List Token} (hR : Ready s) (hT : s.target = T) (hs : s.rest = x :: r) (hx : x.kind ≠ .eof)
    (h : Parse.parseFor (f + 1) s = .ok st s') :
    Ready s' ∧ Kept s s' ∧ st.wf T s.inFunction (s.loopDepth != 0) = true ∧
      (st.openIf = true → ∀ u ∈ s'.rest.head?, u.kind ≠ .keyword "else") ∧ st.isDecl = false ∧ StmtOK T st := by
  simp only [Parse.parseFor] at h
  rw [Parse.bind_eq (advance_past hR hs hx)] at h
  have hR₁ := hR.past hs (hR.more hs hx)
  rw [Parse.bind_ok] at h; obtain ⟨lp, s₂, hlp, h⟩ := h
  obtain ⟨_, r₂, _, rfl, hR₂⟩ := expectPunct_inv hR₁ hlp
  rw [Parse.bind_ok] at h; obtain ⟨init, s₃, hinit, h⟩ := h
  obtain ⟨hR₃, hK₃, hiw, hiok⟩ := forInit_inv hR₂ hT hinit
  rw [Parse.bind_ok] at h; obtain ⟨sm, s₄, hsm, h⟩ := h
  obtain ⟨_, r₄, _, rfl, hR₄⟩ := expectPunct_inv hR₃ hsm
  have hK₄ : Kept s (past s₃ sm r₄) := (Kept.past _ _ _).trans ((Kept.past _ _ _).trans (hK₃.trans (Kept.past _ _ _)))
  rw [Parse.bind_ok] at h; obtain ⟨test, s₅, htest, h⟩ := h
  obtain ⟨hR₅, hK₅, htw, htok⟩ := forPart_inv (.inl rfl) hR₄ (hK₄.target_eq.trans hT) htest
  rw [Parse.bind_ok] at h; obtain ⟨sm₂, s₆, hsm₂, h⟩ := h
  obtain ⟨_, r₆, _, rfl, hR₆⟩ := expectPunct_inv hR₅ hsm₂
  have hK₆ : Kept s (past s₅ sm₂ r₆) := hK₄.trans (hK₅.trans (Kept.past _ _ _))
  rw [Parse.bind_ok] at h; obtain ⟨update, s₇, hupdate, h⟩ := h
  obtain ⟨hR₇, hK₇, huw, huok⟩ := forPart_inv (.inr rfl) hR₆ (hK₆.target_eq.trans hT) hupdate
  rw [Parse.bind_ok] at h; obtain ⟨rp, s₈, hrp, h⟩ := h
  obtain ⟨_, r₈, _, rfl, hR₈⟩ := expectPunct_inv hR₇ hrp
  have hK₈ : Kept s (past s₇ rp r₈) := hK₆.trans (hK₇.trans (Kept.past _ _ _))
  rw [Parse.bind_ok] at h; obtain ⟨body, s₉, hbody, h⟩ := h
  obtain ⟨hR₉, hK₉, hbw, hbo, hbd, hbok⟩ := withLoop_inv hB hR₈ (hK₈.target_eq.trans hT) hbody
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  refine ⟨hR₉, hK₈.trans hK₉, ?_, by simpa [Stmt.openIf] using hbo, by simp [Stmt.isDecl],
    StmtOK.counted hiok htok huok hbok⟩
  simp only [Stmt.wf, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨hiw, htw⟩, huw⟩, hbd⟩, ?_⟩
  rw [← hK₈.inFunction_eq]; exact hbw

/-- `( test )`, after `if` or `while`. -/
theorem parenTest_inv {β : Type} {T : Edition} {s s' : ParseState} {K : Expr → ParseM β} {res : β}
    (hR : Ready s) (hT : s.target = T)
    (h : (Parse.expectPunct "(" >>= fun _ => Parse.budget >>= fun b => Parse.parseExpression b >>= fun test =>
      Parse.expectPunct ")" >>= fun _ => K test) s = .ok res s') :
    ∃ test s₁, Ready s₁ ∧ Kept s s₁ ∧ test.wfParen T = true ∧ WordsOK T test.words ∧ K test s₁ = .ok res s' := by
  rw [Parse.bind_ok] at h; obtain ⟨lp, s₁, hlp, h⟩ := h
  obtain ⟨_, r₁, _, rfl, hR₁⟩ := expectPunct_inv hR hlp
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h; obtain ⟨test, s₂, ht, h⟩ := h
  have gt := (exprs_give T _).1 _ _ _ hR₁ hT ht
  rw [Parse.bind_ok] at h; obtain ⟨rp, s₃, hrp, h⟩ := h
  obtain ⟨_, r₃, _, rfl, hR₃⟩ := expectPunct_inv gt.ready hrp
  exact ⟨test, _, hR₃, (Kept.past _ _ _).trans (gt.kept.trans (Kept.past _ _ _)),
    by simp only [Expr.wfParen, Bool.and_eq_true]; exact ⟨gt.wf, gt.after _ (follows_end (.inr rfl))⟩, gt.ok, h⟩

/-- A statement that is not a declaration, read by `parseExpressionStatement`, is well formed. -/
theorem exprStmt_gives {T : Edition} {n : Nat} {s s' : ParseState} {st : Stmt} {x : Token} {r : List Token}
    (hR : Ready s) (hT : s.target = T) (hs : s.rest = x :: r) (hx : startsExprStmt (some x.kind) = true)
    (h : Parse.parseExpressionStatement n s = .ok st s') :
    Ready s' ∧ Kept s s' ∧ st.wf T s.inFunction (s.loopDepth != 0) = true ∧
      (st.openIf = true → ∀ u ∈ s'.rest.head?, u.kind ≠ .keyword "else") ∧
      (st.isDecl = true → ∀ x ∈ s.rest.head?, x.kind = .keyword "const" ∨ x.kind = .ident "let") ∧
      StmtOK T st := by
  cases n with
  | zero => simp only [Parse.parseExpressionStatement] at h; exact absurd h (outOfFuel_ne_ok _ _ _)
  | succ m => ?_
  obtain ⟨hR', hK', sp, e, rfl, hw, ha, hh, hok⟩ := parseExpressionStatement_inv hR hT hs h
  refine ⟨hR', hK', ?_, by simp [Stmt.openIf], by simp [Stmt.isDecl], StmtOK.exprStmt hok⟩
  simp only [Stmt.wf, Bool.and_eq_true]
  exact ⟨⟨hw, ha⟩, by rw [hh]; exact hx⟩

/-- `parseClauseBreak` gives a `break`. -/
theorem parseClauseBreak_inv {s s' : ParseState} {st : Stmt} {x : Token} {r : List Token} (hR : Ready s)
    (hs : s.rest = x :: r) (hx : x.kind ≠ .eof) (h : Parse.parseClauseBreak s = .ok st s') :
    Ready s' ∧ Kept s s' ∧ ∃ sp, st = .breakStmt sp := by
  simp only [Parse.parseClauseBreak] at h
  rw [Parse.bind_eq (advance_past hR hs hx)] at h
  have hR₁ := hR.past hs (hR.more hs hx)
  obtain ⟨y, r₁, hs₁⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
  obtain ⟨_, h⟩ := fail_inv h
  rw [Parse.bind_ok] at h; obtain ⟨_, s₂, hend, h⟩ := h
  obtain ⟨hR₂, hK₂⟩ := endStatement_inv hR₁ hend
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨hR₂, (Kept.past _ _ _).trans hK₂, _, rfl⟩

/-- One step of the loop over the statements of a clause keeps its invariant. -/
theorem clauseStep_inv {T : Edition} {p : ParseM Stmt} (hp : GivesS T p) {s₀ : ParseState}
    {items items' : Array Stmt} {b : Bool} {st st' : ParseState} (hT : s₀.target = T)
    (hI : Ready st ∧ Kept s₀ st ∧
      ∀ x ∈ items.toList, (x.isBreak = true ∨ x.wf T s₀.inFunction (s₀.loopDepth != 0) = true) ∧ StmtOK T x)
    (h : Parse.clauseStep p items st = .ok (items', b) st') :
    Ready st' ∧ Kept s₀ st' ∧ ∀ x ∈ items'.toList, (x.isBreak = true ∨ x.wf T s₀.inFunction (s₀.loopDepth != 0) = true) ∧ StmtOK T x := by
  obtain ⟨hR, hK, hall⟩ := hI
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.clauseStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : (x.isPunct "}" || x.isKeyword "case" || x.isKeyword "default") = true
  · rw [if_pos hc] at h; simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR, hK, hall⟩
  rw [if_neg hc, Parse.pure_bind] at h
  by_cases he : x.isEof = true
  · rw [if_pos he] at h; exact absurd h (unexpected_bind_ne_ok _ _ _ _ _ _)
  rw [if_neg he, Parse.pure_bind] at h
  by_cases hb : x.isKeyword "break" = true
  · rw [if_pos hb, Parse.bind_ok] at h
    obtain ⟨y, s₁, hy, h⟩ := h
    have hx : x.kind ≠ .eof := by
      have : x.kind = .keyword "break" := by simpa [Token.isKeyword] using hb
      rw [this]; simp
    obtain ⟨hR₁, hK₁, sp, rfl⟩ := parseClauseBreak_inv hR hs hx hy
    simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    refine ⟨hR₁, hK.trans hK₁, fun x' hx' => ?_⟩
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx'
    rcases hx' with hx' | rfl
    · exact hall x' hx'
    · exact ⟨.inl rfl, StmtOK.brk⟩
  rw [if_neg hb, Parse.pure_bind, Parse.bind_ok] at h
  obtain ⟨y, s₁, hy, h⟩ := h
  obtain ⟨hR₁, hK₁, hw, _, _, hok⟩ := hp _ _ _ hR (hK.target_eq.trans hT) hy
  simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
  refine ⟨hR₁, hK.trans hK₁, fun x' hx' => ?_⟩
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx'
  rcases hx' with hx' | rfl
  · exact hall x' hx'
  · exact ⟨.inr (by rw [← hK.inFunction_eq, ← hK.loopDepth_eq]; exact hw), hok⟩

/-- What `parseClause` gives: a clause whose test `Expr.caseWF` accepts, and
whose statements `Stmt.wf` accepts in the state's function and loop. -/
def GivesC (T : Edition) (p : ParseM (Option Expr × List Stmt)) : Prop :=
  ∀ s c s', Ready s → s.target = T → p s = .ok c s' →
    Ready s' ∧ Kept s s' ∧ Expr.caseWF T c.1 = true ∧
      (∀ x ∈ c.2, (x.isBreak = true ∨ x.wf T s.inFunction (s.loopDepth != 0) = true)) ∧ ClauseOK T c

/-- The `:` of a clause and its statements. -/
theorem clauseTail_inv {T : Edition} {f : Nat} (hS : GivesS T (Parse.parseStatement f)) {s₂ s' : ParseState}
    {y : Option Expr} {c : Option Expr × List Stmt} (hR : Ready s₂) (hT : s₂.target = T)
    (h : (Parse.expectPunct ":" >>= fun _ => Parse.budget >>= fun b =>
      Parse.iterate b #[] (Parse.clauseStep (Parse.parseStatement f)) >>= fun body => pure (y, body.toList)) s₂ =
        .ok c s') :
    Ready s' ∧ Kept s₂ s' ∧ c.1 = y ∧
      ∀ x ∈ c.2, (x.isBreak = true ∨ x.wf T s₂.inFunction (s₂.loopDepth != 0) = true) ∧ StmtOK T x := by
  rw [Parse.bind_ok] at h; obtain ⟨colon, s₃, hc, h⟩ := h
  obtain ⟨_, r₃, _, rfl, hR₃⟩ := expectPunct_inv hR hc
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h; obtain ⟨items, s₄, hit, h⟩ := h
  obtain ⟨hR₄, hK₄, hall⟩ := (iterate_inv
    (I := fun a st => Ready st ∧ Kept (past s₂ colon r₃) st ∧
      ∀ x ∈ a.toList, (x.isBreak = true ∨ x.wf T (past s₂ colon r₃).inFunction ((past s₂ colon r₃).loopDepth != 0) = true) ∧
        StmtOK T x)
    (fun _ _ _ _ _ hI hst => clauseStep_inv (s₀ := past s₂ colon r₃) hS
      (show (past s₂ colon r₃).target = T from hT) hI hst)
    _ #[] _ items s₄ ⟨hR₃, Kept.refl _, by simp⟩ hit).1
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨hR₄, (Kept.past _ _ _).trans hK₄, rfl, hall⟩

theorem parseClause_gives {T : Edition} {f : Nat} (hS : GivesS T (Parse.parseStatement f)) :
    GivesC T (Parse.parseClause (f + 1)) := by
  intro s c s' hR hT h
  obtain ⟨ct, cb⟩ := c
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseClause] at h
  rw [Parse.bind_ok] at h; obtain ⟨t, s₁, ht, h⟩ := h
  obtain ⟨rfl, hpast⟩ := advance_inv hR hs ht
  by_cases hx : t.kind = .eof
  · rw [if_neg (show ¬ (t.isKeyword "case" = true) by simp [Token.isKeyword, hx]),
      if_neg (show ¬ (t.isKeyword "default" = true) by simp [Token.isKeyword, hx])] at h
    exact absurd h (unexpected_bind_ne_ok _ _ _ _ _ _)
  obtain ⟨rfl, hR₁⟩ := hpast hx
  have hK₁ : Kept s (past s t r) := Kept.past _ _ _
  by_cases hcase : t.isKeyword "case" = true
  · have hkw : t.kind = .keyword "case" := by simpa [Token.isKeyword] using hcase
    rw [if_pos hcase, Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
    obtain ⟨e, s₂, he, h⟩ := h
    have ge := (exprs_give T _).1 _ _ _ hR₁ hT he
    obtain ⟨hfree, h⟩ := pass_inv h
    rw [Parse.pure_bind] at h
    obtain ⟨hR', hK', rfl, hall⟩ := clauseTail_inv hS ge.ready (ge.kept.target_eq.trans hT) h
    have hK₂ : Kept s s₂ := hK₁.trans ge.kept
    have hcw : Word.ok T (keywordWord "case") = true := by
      have := hT ▸ hR.tok (x := t) (by simp [hs]) (by simp [hkw])
      simpa [keywordWord, hkw] using this
    have hok := ge.ok
    refine ⟨hR', hK₂.trans hK', ?_, fun y hy => ?_, ?_, fun y hy => (hall y hy).2⟩
    · simp only [Expr.caseWF, Bool.and_eq_true]; exact ⟨⟨ge.wf, hfree⟩, ge.after _ follows_colon⟩
    · rw [← hK₂.inFunction_eq, ← hK₂.loopDepth_eq]; exact (hall y hy).1
    · simp only [clauseHead]; words_ok
  · rw [if_neg hcase] at h
    by_cases hdef : t.isKeyword "default" = true
    · have hkw : t.kind = .keyword "default" := by simpa [Token.isKeyword] using hdef
      rw [if_pos hdef, Parse.pure_bind] at h
      obtain ⟨hR', hK', rfl, hall⟩ := clauseTail_inv hS hR₁ hT h
      have hdw : Word.ok T (keywordWord "default") = true := by
        have := hT ▸ hR.tok (x := t) (by simp [hs]) (by simp [hkw])
        simpa [keywordWord, hkw] using this
      refine ⟨hR', hK₁.trans hK', rfl, fun y hy => ?_, ?_, fun y hy => (hall y hy).2⟩
      · rw [← hK₁.inFunction_eq, ← hK₁.loopDepth_eq]; exact (hall y hy).1
      · simp only [clauseHead]; words_ok
    · rw [if_neg hdef] at h; exact absurd h (unexpected_bind_ne_ok _ _ _ _ _ _)

/-- One step of the loop over the clauses of a `switch` keeps its invariant. -/
theorem clauseBlockStep_inv {T : Edition} {p : ParseM (Option Expr × List Stmt)} (hp : GivesC T p)
    {s₀ : ParseState} {items items' : Array (Option Expr × List Stmt)} {b : Bool} {st st' : ParseState}
    (hT : s₀.target = T)
    (hI : Ready st ∧ Kept s₀ st ∧ ∀ c ∈ items.toList, Expr.caseWF T c.1 = true ∧
      (∀ x ∈ c.2, (x.isBreak = true ∨ x.wf T s₀.inFunction (s₀.loopDepth != 0) = true)) ∧ ClauseOK T c)
    (h : Parse.blockStep p items st = .ok (items', b) st') :
    Ready st' ∧ Kept s₀ st' ∧ ∀ c ∈ items'.toList, Expr.caseWF T c.1 = true ∧
      (∀ x ∈ c.2, (x.isBreak = true ∨ x.wf T s₀.inFunction (s₀.loopDepth != 0) = true)) ∧ ClauseOK T c := by
  obtain ⟨hR, hK, hall⟩ := hI
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.blockStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : x.isPunct "}" = true
  · rw [if_pos hc] at h; simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR, hK, hall⟩
  rw [if_neg hc, Parse.pure_bind] at h
  by_cases he : x.isEof = true
  · rw [if_pos he] at h; exact absurd h (unexpected_bind_ne_ok _ _ _ _ _ _)
  rw [if_neg he, Parse.pure_bind, Parse.bind_ok] at h
  obtain ⟨y, s₁, hy, h⟩ := h
  obtain ⟨hR₁, hK₁, hw, hbody, hok⟩ := hp _ _ _ hR (hK.target_eq.trans hT) hy
  simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
  refine ⟨hR₁, hK.trans hK₁, fun c hc' => ?_⟩
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hc'
  rcases hc' with hc' | rfl
  · exact hall c hc'
  · exact ⟨hw, fun x hx => by rw [← hK.inFunction_eq, ← hK.loopDepth_eq]; exact hbody x hx, hok⟩

/-- What `parseForOf` or `parseFor` gives, when it starts at a token other than the end of the file. -/
def GivesFor (T : Edition) (p : ParseM Stmt) : Prop :=
  ∀ s st s' x r, Ready s → s.target = T → s.rest = x :: r → x.kind ≠ .eof → p s = .ok st s' →
    Ready s' ∧ Kept s s' ∧ st.wf T s.inFunction (s.loopDepth != 0) = true ∧
      (st.openIf = true → ∀ u ∈ s'.rest.head?, u.kind ≠ .keyword "else") ∧ st.isDecl = false ∧ StmtOK T st

theorem parseStatement_gives {T : Edition} {f : Nat} (hBlk : GivesS T (Parse.parseBlock f))
    (hBr : GivesB T (Parse.parseBranch f)) (hFor : GivesFor T (Parse.parseForOf f))
    (hCnt : GivesFor T (Parse.parseFor f)) (hCl : GivesC T (Parse.parseClause f)) :
    GivesS T (Parse.parseStatement (f + 1)) := by
  intro s st s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  have hne : ∀ {k}, x.kind = k → k ≠ .eof → x.kind ≠ .eof := fun hk hk' => by rw [hk]; exact hk'
  simp only [Parse.parseStatement] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  -- A variable declaration, as the `const` and `let` arm of the `match` gives it.
  have hdecl : (x.kind = .keyword "const" ∨ x.kind = .ident "let") →
      (Parse.parseVarDecl >>= fun decl => Parse.spanFrom x.span.start >>= fun sp => pure (Stmt.varDecl sp decl)) s =
        .ok st s' →
      Ready s' ∧ Kept s s' ∧ st.wf T s.inFunction (s.loopDepth != 0) = true ∧
        (st.openIf = true → ∀ u ∈ s'.rest.head?, u.kind ≠ .keyword "else") ∧
        (st.isDecl = true → ∀ x ∈ s.rest.head?, x.kind = .keyword "const" ∨ x.kind = .ident "let") ∧
        StmtOK T st := by
    intro hk h
    rw [Parse.bind_ok] at h; obtain ⟨d, s₁, hd, h⟩ := h
    obtain ⟨hR₁, hK₁, hdw, hdok⟩ := parseVarDecl_inv hR hT hs (by rcases hk with hk | hk <;> rw [hk] <;> simp) hd
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR₁, hK₁, by simpa [Stmt.wf] using hdw, by simp [Stmt.openIf], fun _ y hy => by
      simp [hs] at hy; subst hy; exact hk, StmtOK.varDecl hdok⟩
  generalize hk : x.kind = k at h
  cases k with
  | punct p =>
    by_cases h1 : p = "{"
    · subst h1; simp only at h; exact hBlk _ _ _ hR hT h
    by_cases h2 : p = ";"
    · subst h2; simp only at h
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs (hne hk (by simp))))] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨hR.past hs (hR.more hs (hne hk (by simp))), Kept.past _ _ _, by simp [Stmt.wf], by simp [Stmt.openIf],
        by simp [Stmt.isDecl], StmtOK.empty⟩
    simp [h1, h2] at h
    exact exprStmt_gives hR hT hs (by rw [hk]; simp [startsExprStmt, h1]) h
  | ident n =>
    by_cases h1 : n = "let"
    · subst h1; simp only at h; exact hdecl (.inr hk) h
    simp [h1] at h
    exact exprStmt_gives hR hT hs (by rw [hk]; simp [startsExprStmt, h1]) h
  | keyword w =>
    by_cases hc : w = "const"
    · subst hc; simp only at h; exact hdecl (.inl hk) h
    by_cases hif : w = "if"
    · subst hif; simp only at h
      have hx := hne hk (by simp)
      have hR₁ := hR.past hs (hR.more hs hx)
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hx))] at h
      obtain ⟨test, s₁, hR₂, hK₂, htw, htok, h⟩ := parenTest_inv hR₁ hT h
      rw [Parse.bind_ok] at h; obtain ⟨tb, s₃, htb, h⟩ := h
      have hT₂ : s₁.target = T := by rw [hK₂.target_eq]; exact hT
      obtain ⟨hR₃, hK₃, htbw, htbo, htbd, htbok⟩ := hBr _ _ _ hR₂ hT₂ htb
      obtain ⟨y, r₃, hs₃⟩ := hR₃.cons
      rw [Parse.bind_eq (Parse.peek_eq hs₃)] at h
      have hfn : s₁.inFunction = s.inFunction := hK₂.inFunction_eq
      have hld : s₁.loopDepth = s.loopDepth := hK₂.loopDepth_eq
      by_cases he : y.isKeyword "else" = true
      · rw [if_pos he] at h
        have hyk : y.kind = .keyword "else" := by simpa [Token.isKeyword] using he
        have hy : y.kind ≠ .eof := by rw [hyk]; simp
        rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₃ hs₃ hy)), Parse.bind_ok] at h
        obtain ⟨eb, s₄, heb, h⟩ := h
        have hT₃ : (past s₃ y r₃).target = T := by
          rw [show (past s₃ y r₃).target = s₃.target from rfl, hK₃.target_eq, hT₂]
        obtain ⟨hR₄, hK₄, hebw, hebo, hebd, hebok⟩ := hBr _ _ _ (hR₃.past hs₃ (hR₃.more hs₃ hy)) hT₃ heb
        rw [Parse.pure_bind, Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
        have hK : Kept s s₃ := (Kept.past _ _ _).trans (hK₂.trans hK₃)
        refine ⟨hR₄, hK.trans ((Kept.past _ _ _).trans hK₄), ?_, by simpa [Stmt.openIf] using hebo,
          by simp [Stmt.isDecl], StmtOK.ifElse htok htbok hebok⟩
        have hto : tb.openIf = false := by
          cases hto : tb.openIf
          · rfl
          · exact absurd hyk (htbo hto y (by simp [hs₃]))
        simp only [Stmt.wf, Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨⟨⟨⟨⟨htw, htbd⟩, by rw [← hfn, ← hld]; exact htbw⟩, hto⟩, hebd⟩, ?_⟩
        rw [← hK.inFunction_eq, ← hK.loopDepth_eq]
        simpa [show (past s₃ y r₃).inFunction = s₃.inFunction from rfl,
          show (past s₃ y r₃).loopDepth = s₃.loopDepth from rfl] using hebw
      · rw [if_neg he, Parse.pure_bind, Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨hR₃, (Kept.past _ _ _).trans (hK₂.trans hK₃), ?_, fun _ u hu => ?_, by simp [Stmt.isDecl],
          StmtOK.ifThen htok htbok⟩
        · simp only [Stmt.wf, Bool.and_eq_true, Bool.not_eq_true']
          exact ⟨⟨htw, htbd⟩, by rw [← hfn, ← hld]; exact htbw⟩
        · simp [hs₃] at hu; subst hu; simpa [Token.isKeyword] using he
    by_cases hfor : w = "for"
    · subst hfor; simp only at h
      rw [Parse.bind_eq (Parse.countedFor_eq s)] at h
      split at h
      · obtain ⟨hR', hK', hw, ho, hd, hok⟩ := hCnt _ _ _ x r hR hT hs (hne hk (by simp)) h
        exact ⟨hR', hK', hw, ho, by simp [hd], hok⟩
      · obtain ⟨hR', hK', hw, ho, hd, hok⟩ := hFor _ _ _ x r hR hT hs (hne hk (by simp)) h
        exact ⟨hR', hK', hw, ho, by simp [hd], hok⟩
    by_cases hwhile : w = "while"
    · subst hwhile; simp only at h
      have hx := hne hk (by simp)
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hx))] at h
      obtain ⟨test, s₁, hR₂, hK₂, htw, htok, h⟩ := parenTest_inv (hR.past hs (hR.more hs hx)) hT h
      rw [Parse.bind_ok] at h; obtain ⟨body, s₃, hb, h⟩ := h
      obtain ⟨hR₃, hK₃, hbw, hbo, hbd, hbok⟩ := withLoop_inv hBr hR₂ (by rw [hK₂.target_eq]; exact hT) hb
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      have hK : Kept s s₁ := (Kept.past _ _ _).trans hK₂
      refine ⟨hR₃, hK.trans hK₃, ?_, by simpa [Stmt.openIf] using hbo, by simp [Stmt.isDecl],
        StmtOK.while htok hbok⟩
      simp only [Stmt.wf, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨⟨htw, hbd⟩, by rw [← hK.inFunction_eq]; exact hbw⟩
    by_cases hret : w = "return"
    · subst hret; simp only at h
      have hx := hne hk (by simp)
      have hR₁ := hR.past hs (hR.more hs hx)
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hx)), get_bind] at h
      obtain ⟨hfn, h⟩ := pass_inv h
      obtain ⟨y, r₁, hs₁⟩ := hR₁.cons
      rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
      by_cases hv : (!(y.isPunct ";" || y.isPunct "}" || y.isEof || y.newlineBefore)) = true
      · rw [if_pos hv, Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
        obtain ⟨e, s₂, he, h⟩ := h
        have ge := (exprs_give T _).1 _ _ _ hR₁ hT he
        rw [Parse.pure_bind, Parse.bind_ok] at h; obtain ⟨_, s₃, hend, h⟩ := h
        obtain ⟨hR₃, hK₃⟩ := endStatement_inv ge.ready hend
        rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨hR₃, (Kept.past _ _ _).trans (ge.kept.trans hK₃), ?_, by simp [Stmt.openIf], by simp [Stmt.isDecl],
          StmtOK.retSome ge.ok⟩
        simp only [Stmt.wf, Bool.and_eq_true]
        exact ⟨⟨hfn, ge.wf⟩, ge.after _ (follows_end (.inl rfl))⟩
      · rw [if_neg hv, Parse.pure_bind, Parse.bind_ok] at h; obtain ⟨_, s₃, hend, h⟩ := h
        obtain ⟨hR₃, hK₃⟩ := endStatement_inv hR₁ hend
        rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨hR₃, (Kept.past _ _ _).trans hK₃, by simpa [Stmt.wf] using hfn, by simp [Stmt.openIf],
          by simp [Stmt.isDecl], StmtOK.retNone⟩
    by_cases hb : w = "break"
    · subst hb; simp only at h
      have hx := hne hk (by simp)
      have hR₁ := hR.past hs (hR.more hs hx)
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hx)), get_bind] at h
      obtain ⟨hloop, h⟩ := fail_inv h
      obtain ⟨y, r₁, hs₁⟩ := hR₁.cons
      rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
      obtain ⟨_, h⟩ := fail_inv h
      rw [Parse.bind_ok] at h; obtain ⟨_, s₂, hend, h⟩ := h
      obtain ⟨hR₂, hK₂⟩ := endStatement_inv hR₁ hend
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      have hl : (s.loopDepth != 0) = true := by simpa using hloop
      refine ⟨hR₂, (Kept.past _ _ _).trans hK₂, ?_, ?_, ?_, ?_⟩ <;> split <;>
        first | exact StmtOK.brk | exact StmtOK.cont | simp [Stmt.wf, Stmt.openIf, Stmt.isDecl, hl]
    by_cases hcn : w = "continue"
    · subst hcn; simp only at h
      have hx := hne hk (by simp)
      have hR₁ := hR.past hs (hR.more hs hx)
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hx)), get_bind] at h
      obtain ⟨hloop, h⟩ := fail_inv h
      obtain ⟨y, r₁, hs₁⟩ := hR₁.cons
      rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
      obtain ⟨_, h⟩ := fail_inv h
      rw [Parse.bind_ok] at h; obtain ⟨_, s₂, hend, h⟩ := h
      obtain ⟨hR₂, hK₂⟩ := endStatement_inv hR₁ hend
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      have hl : (s.loopDepth != 0) = true := by simpa using hloop
      refine ⟨hR₂, (Kept.past _ _ _).trans hK₂, ?_, ?_, ?_, ?_⟩ <;> split <;>
        first | exact StmtOK.brk | exact StmtOK.cont | simp [Stmt.wf, Stmt.openIf, Stmt.isDecl, hl]
    by_cases hsw : w = "switch"
    · subst hsw; simp only at h
      have hx := hne hk (by simp)
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hx))] at h
      obtain ⟨disc, s₁, hR₂, hK₂, hdw, hdok, h⟩ := parenTest_inv (hR.past hs (hR.more hs hx)) hT h
      rw [Parse.bind_ok] at h; obtain ⟨lb, s₃, hlb, h⟩ := h
      obtain ⟨_, r₃, _, rfl, hR₃⟩ := expectPunct_inv hR₂ hlb
      rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h; obtain ⟨items, s₄, hit, h⟩ := h
      have hK : Kept s (past s₁ lb r₃) := (Kept.past _ _ _).trans (hK₂.trans (Kept.past _ _ _))
      have hT₃ : (past s₁ lb r₃).target = T := hK.target_eq.trans hT
      obtain ⟨hR₄, hK₄, hall⟩ := (iterate_inv
        (I := fun a st => Ready st ∧ Kept (past s₁ lb r₃) st ∧ ∀ c ∈ a.toList, Expr.caseWF T c.1 = true ∧
          (∀ x ∈ c.2, x.isBreak = true ∨ x.wf T (past s₁ lb r₃).inFunction ((past s₁ lb r₃).loopDepth != 0) = true) ∧
            ClauseOK T c)
        (fun _ _ _ _ _ hI hst => clauseBlockStep_inv (s₀ := past s₁ lb r₃) hCl hT₃ hI hst)
        _ #[] _ items s₄ ⟨hR₃, Kept.refl _, by simp⟩ hit).1
      rw [Parse.bind_ok] at h; obtain ⟨rb, s₅, hrb, h⟩ := h
      obtain ⟨_, r₅, _, rfl, hR₅⟩ := expectPunct_inv hR₄ hrb
      obtain ⟨hnd, h⟩ := fail_inv h
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨hR₅, hK.trans (hK₄.trans (Kept.past _ _ _)), ?_, by simp [Stmt.openIf], by simp [Stmt.isDecl],
        StmtOK.switch hdok (fun c hc => (hall c hc).2.2)⟩
      simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨hdw, by omega⟩, Stmt.clausesWF_iff.mpr fun c hc => ⟨(hall c hc).1, Stmt.allClauseWF_iff.mpr
        fun x hx => by rw [← hK.inFunction_eq, ← hK.loopDepth_eq]; exact (hall c hc).2.1 x hx⟩⟩
    by_cases hth : w = "throw"
    · subst hth; simp only at h
      have hx := hne hk (by simp)
      have hR₁ := hR.past hs (hR.more hs hx)
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR hs hx))] at h
      obtain ⟨y, r₁, hs₁⟩ := hR₁.cons
      rw [Parse.bind_eq (Parse.peek_eq hs₁)] at h
      obtain ⟨_, h⟩ := fail_inv h
      rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
      obtain ⟨e, s₂, he, h⟩ := h
      have ge := (exprs_give T _).1 _ _ _ hR₁ hT he
      rw [Parse.bind_ok] at h; obtain ⟨_, s₃, hend, h⟩ := h
      obtain ⟨hR₃, hK₃⟩ := endStatement_inv ge.ready hend
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨hR₃, (Kept.past _ _ _).trans (ge.kept.trans hK₃), ?_, by simp [Stmt.openIf], by simp [Stmt.isDecl],
        StmtOK.throw ge.ok⟩
      simp only [Stmt.wf, Bool.and_eq_true]
      exact ⟨ge.wf, ge.after _ (follows_end (.inl rfl))⟩
    by_cases he : w = "true" ∨ w = "false" ∨ w = "null" ∨ w = "typeof" ∨ w = "void" ∨ w = "new"
    · rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at h <;>
        exact exprStmt_gives hR hT hs (by rw [hk]; simp [startsExprStmt]) h
    simp only [not_or] at he
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := he
    simp at h
  | number v | bigint v | string v | eof =>
    simp only at h
    exact exprStmt_gives hR hT hs (by rw [hk]; simp [startsExprStmt]) h

/-- Every function of the statement parser gives what `GivesS` states, for
every amount of fuel. -/
theorem stmts_give (T : Edition) : ∀ f : Nat,
    GivesS T (Parse.parseStatement f) ∧ GivesB T (Parse.parseBranch f) ∧ GivesS T (Parse.parseBlock f) ∧
      GivesFor T (Parse.parseForOf f) ∧ GivesFor T (Parse.parseFor f) ∧ GivesC T (Parse.parseClause f)
  | 0 => ⟨fun _ _ _ _ _ h => absurd h (by simp only [Parse.parseStatement]; exact outOfFuel_ne_ok _ _ _),
      fun _ _ _ _ _ h => absurd h (by simp only [Parse.parseBranch]; exact outOfFuel_ne_ok _ _ _),
      fun _ _ _ _ _ h => absurd h (by simp only [Parse.parseBlock]; exact outOfFuel_ne_ok _ _ _),
      fun _ _ _ _ _ _ _ _ _ h => absurd h (by simp only [Parse.parseForOf]; exact outOfFuel_ne_ok _ _ _),
      fun _ _ _ _ _ _ _ _ _ h => absurd h (by simp only [Parse.parseFor]; exact outOfFuel_ne_ok _ _ _),
      fun _ _ _ _ _ h => absurd h (by simp only [Parse.parseClause]; exact outOfFuel_ne_ok _ _ _)⟩
  | f + 1 =>
    let ⟨hS, hBr, hBlk, hFor, hCnt, hCl⟩ := stmts_give T f
    ⟨parseStatement_gives hBlk hBr hFor hCnt hCl, parseBranch_gives hS, parseBlock_gives hS,
      fun _ _ _ _ _ hR hT hs hx h => parseForOf_inv hBr hR hT hs hx h,
      fun _ _ _ _ _ hR hT hs hx h => parseFor_inv hBr hR hT hs hx h, parseClause_gives hS⟩

/-! ### Declarations -/

/-- Every line that `d` prints has words that lex back. -/
def DeclOK (T : Edition) (d : Decl) : Prop := ∀ l ∈ d.lines, WordsOK T l.2

section
variable {T : Edition} {sp : Span}

theorem DeclOK.import {names : List ImportName} {source : String} (h : ∀ n ∈ names, WordsOK T n.words) :
    DeclOK T (.import sp names source) := by
  have := wordsOK_enclose (T := T) (o := "{") (c := "}") (items := names.map ImportName.words) (by decide)
    (by decide) (by intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact h n hn)
  intro l hl; simp only [Decl.lines, List.mem_singleton] at hl; subst hl
  words_ok

theorem DeclOK.exports {names : List ImportName} {source : Option String} (h : ∀ n ∈ names, WordsOK T n.words) :
    DeclOK T (.exports sp names source) := by
  have := wordsOK_enclose (T := T) (o := "{") (c := "}") (items := names.map ImportName.words) (by decide)
    (by decide) (by intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact h n hn)
  intro l hl; simp only [Decl.lines, List.mem_singleton] at hl; subst hl
  cases source <;> simp only [fromWords] <;> words_ok

theorem DeclOK.function {exported : Bool} {name : String} {tps : List String} {params : List Param}
    {rt : Option TypeExpr} {body : Stmt} (hn : Word.ok T (identWord name) = true)
    (htp : WordsOK T (typeParamWords tps)) (hp : ∀ p ∈ params, WordsOK T p.words)
    (hr : ∀ t, rt = some t → WordsOK T t.words) (hb : StmtOK T body) :
    DeclOK T (.function sp exported name tps params rt body) := by
  have h0 := htp
  have h1 := exportWords_ok T exported
  have h2 := wordsOK_enclose (T := T) (o := "(") (c := ")") (items := params.map Param.words) (by decide)
    (by decide) (by intro x hx; obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx; exact hp p hp')
  have h3 := typeAnnotation_ok hr
  intro l hl
  simp only [Decl.lines, List.mem_cons] at hl
  rcases hl with rfl | hl
  · words_ok
  · exact hb 0 l hl

theorem DeclOK.interface {exported : Bool} {name : String} {tps : List String} {fields : List Field}
    (hn : Word.ok T (identWord name) = true) (htp : WordsOK T (typeParamWords tps))
    (hf : ∀ f ∈ fields, WordsOK T f.words) :
    DeclOK T (.interface sp exported name tps fields) := by
  have h0 := htp
  have h1 := exportWords_ok T exported
  intro l hl
  simp only [Decl.lines, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | ⟨f, hf', rfl⟩) | rfl
  · words_ok
  · exact hf f hf'
  · words_ok

theorem DeclOK.typeAlias {exported : Bool} {name : String} {tps : List String} {type : TypeExpr}
    (hn : Word.ok T (identWord name) = true) (htp : WordsOK T (typeParamWords tps)) (ht : WordsOK T type.words) :
    DeclOK T (.typeAlias sp exported name tps type) := by
  have h0 := htp
  have h1 := exportWords_ok T exported
  intro l hl; simp only [Decl.lines, List.mem_singleton] at hl; subst hl
  words_ok

theorem DeclOK.enum {exported : Bool} {name : String} {members : List EnumMember}
    (hn : Word.ok T (identWord name) = true) (hm : ∀ m ∈ members, WordsOK T m.words) :
    DeclOK T (.enum sp exported name members) := by
  have h1 := exportWords_ok T exported
  intro l hl
  simp only [Decl.lines, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | ⟨m, hm', rfl⟩) | rfl
  · words_ok
  · exact hm m hm'
  · words_ok

theorem DeclOK.exportedVar {d : VarDecl} (hd : WordsOK T d.words) : DeclOK T (.exportedVar sp d) := by
  intro l hl; simp only [Decl.lines, List.mem_singleton] at hl; subst hl
  words_ok

theorem DeclOK.stmt {st : Stmt} (h : StmtOK T st) : DeclOK T (.stmt st) := fun l hl => h 0 l hl

end

/-- The steps of the loop over a list keep every item well formed. -/
theorem listStep_wf {α : Type} {T : Edition} {P : α → Prop} {close : String} {refuse : Token → ParseM Unit}
    {p : ParseM α} (hp : GivesW T P p) (hrefuse : ∀ t s s', refuse t s = .ok () s' → s' = s) {s₀ : ParseState}
    (hT : s₀.target = T) {items items' : Array α} {b : Bool} {st st' : ParseState}
    (hI : Ready st ∧ Kept s₀ st ∧ ∀ x ∈ items.toList, P x)
    (h : Parse.listStep close refuse p items st = .ok (items', b) st') :
    Ready st' ∧ Kept s₀ st' ∧ ∀ x ∈ items'.toList, P x := by
  obtain ⟨hR, hK, hwf⟩ := hI
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.listStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : x.isPunct close = true
  · rw [if_pos hc] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR, hK, hwf⟩
  rw [if_neg hc, Parse.pure_bind, Parse.bind_ok] at h
  obtain ⟨_, s₁, hr1, h⟩ := h
  obtain rfl := hrefuse _ _ _ hr1
  rw [Parse.bind_ok] at h; obtain ⟨y, s₂, hy, h⟩ := h
  obtain ⟨hR₂, hK₂, hyw⟩ := hp _ _ _ hR (hK.target_eq.trans hT) hy
  have hwf' : ∀ x ∈ (items.push y).toList, P x := by
    intro x' hx'
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx'
    rcases hx' with hx' | rfl
    · exact hwf x' hx'
    · exact hyw
  obtain ⟨z, r₂, hs₂⟩ := hR₂.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
  by_cases hz : z.isPunct "," = true
  · have hne : z.kind ≠ .eof := by simp [Token.isPunct] at hz; rw [hz]; simp
    rw [if_pos hz, Parse.bind_eq (Parse.discard_eq (advance_past hR₂ hs₂ hne))] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR₂.past hs₂ (hR₂.more hs₂ hne), hK.trans (hK₂.trans (Kept.past _ _ _)), hwf'⟩
  · rw [if_neg hz] at h
    by_cases hz2 : (!z.isPunct close) = true
    · rw [if_pos hz2] at h; exact absurd h (unexpected_bind_ne_ok _ _ _ _ _ _)
    · rw [if_neg hz2, Parse.pure_bind] at h
      simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
      exact ⟨hR₂, hK.trans hK₂, hwf'⟩

theorem blockStep_wf {α : Type} {T : Edition} {P : α → Prop} {p : ParseM α} (hp : GivesW T P p)
    {s₀ : ParseState} (hT : s₀.target = T) {items items' : Array α} {b : Bool} {st st' : ParseState}
    (hI : Ready st ∧ Kept s₀ st ∧ ∀ x ∈ items.toList, P x)
    (h : Parse.blockStep p items st = .ok (items', b) st') :
    Ready st' ∧ Kept s₀ st' ∧ ∀ x ∈ items'.toList, P x := by
  obtain ⟨hR, hK, hall⟩ := hI
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.blockStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : x.isPunct "}" = true
  · rw [if_pos hc] at h; simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR, hK, hall⟩
  rw [if_neg hc, Parse.pure_bind] at h
  by_cases he : x.isEof = true
  · rw [if_pos he] at h; exact absurd h (unexpected_bind_ne_ok _ _ _ _ _ _)
  rw [if_neg he, Parse.pure_bind, Parse.bind_ok] at h
  obtain ⟨y, s₁, hy, h⟩ := h
  obtain ⟨hR₁, hK₁, hw⟩ := hp _ _ _ hR (hK.target_eq.trans hT) hy
  simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
  refine ⟨hR₁, hK.trans hK₁, fun x' hx' => ?_⟩
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx'
  rcases hx' with hx' | rfl
  · exact hall x' hx'
  · exact hw

/-- `advance` keeps the state ready, also at the end of the file. -/
theorem advance_ready {s s' : ParseState} {t : Token} (hR : Ready s) (h : Parse.advance s = .ok t s') :
    Ready s' ∧ Kept s s' := by
  obtain ⟨x, r, hs⟩ := hR.cons
  cases r with
  | cons u r' =>
    obtain ⟨_, rfl⟩ := ok_unique h (Parse.advance_cons hs (by simp))
    exact ⟨hR.past hs (by simp), Kept.past _ _ _⟩
  | nil =>
    simp only [Parse.advance, hs, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, set,
      MonadStateOf.set, EStateM.set, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
    obtain ⟨_, rfl⟩ := h
    refine ⟨⟨⟨by simp, by rw [hR.1.2, hs]⟩, by have := hR.2.1; rw [hs] at this; simpa using this, hR.2.2.1,
      fun t ht => hR.2.2.2 t (by rw [hs]; simpa using ht)⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

theorem discard_advance_ready {s s' : ParseState} (hR : Ready s) (h : (discard Parse.advance) s = .ok () s') :
    Ready s' ∧ Kept s s' := by
  simp only [discard, Functor.mapConst, Function.comp_apply, EStateM.map] at h
  split at h
  · rename_i t s₁ ha; simp only [EStateM.Result.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
    exact advance_ready hR ha
  · simp at h

/-- An action that always refuses. -/
def Refuses {α : Type} (a : ParseM α) : Prop := ∀ s, ∃ e s', a s = .error e s'

theorem Refuses.bind {α β : Type} {a : ParseM α} (ha : Refuses a) (K : α → ParseM β) (s s' : ParseState) (r : β) :
    (a >>= K) s ≠ .ok r s' := by
  obtain ⟨e, s'', he⟩ := ha s
  intro hc
  rw [Parse.bind_ok] at hc
  obtain ⟨_, _, h1, _⟩ := hc
  rw [he] at h1; cases h1

theorem unexpected_refuses {α : Type} (t : Token) (m : String) : Refuses (Parse.unexpected (A := α) t m) :=
  fun _ => ⟨_, _, rfl⟩

theorem refuseImport_refuses {α : Type} (t : Token) : Refuses (Parse.refuseImport (A := α) t) :=
  fun _ => ⟨_, _, rfl⟩

theorem refuseEnumMember_refuses {α : Type} (t : Token) : Refuses (Parse.refuseEnumMember (A := α) t) :=
  fun _ => ⟨_, _, rfl⟩

theorem pass_err {β : Type} {c : Prop} [Decidable c] {a : ParseM PUnit} (ha : Refuses a) {K : PUnit → ParseM β}
    {s s' : ParseState} {r : β} (h : (if c then pure PUnit.unit >>= K else a >>= K) s = .ok r s') :
    c ∧ K () s = .ok r s' := by
  by_cases hc : c
  · rw [if_pos hc, Parse.pure_bind] at h; exact ⟨hc, h⟩
  · rw [if_neg hc] at h; exact absurd h (ha.bind _ _ _ _)

theorem fail_err {β : Type} {c : Prop} [Decidable c] {a : ParseM PUnit} (ha : Refuses a) {K : PUnit → ParseM β}
    {s s' : ParseState} {r : β} (h : (if c then a >>= K else pure PUnit.unit >>= K) s = .ok r s') :
    ¬c ∧ K () s = .ok r s' := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact absurd h (ha.bind _ _ _ _)
  · rw [if_neg hc, Parse.pure_bind] at h; exact ⟨hc, h⟩

/-- An optional `advance`, run by an `if`: the state stays ready. -/
theorem seq_advance {β : Type} {c : Prop} [Decidable c] {K : PUnit → ParseM β} {s s' : ParseState} {r : β}
    (hR : Ready s) (h : (if c then discard Parse.advance >>= K else pure PUnit.unit >>= K) s = .ok r s') :
    ∃ s₁, Ready s₁ ∧ Kept s s₁ ∧ K () s₁ = .ok r s' := by
  obtain ⟨s₁, h1, h2, hk⟩ := seq_inv h
  by_cases hc : c
  · obtain ⟨hR₁, hK₁⟩ := discard_advance_ready hR (h1 hc); exact ⟨s₁, hR₁, hK₁, hk⟩
  · have e := h2 hc; subst e; exact ⟨_, hR, Kept.refl _, hk⟩

theorem parseField_wf {T : Edition} :
    GivesW T (fun f : Field => f.type.wf = true ∧ WordsOK T f.words) Parse.parseField := by
  intro s fld s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseField] at h
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.peekAt_rest s 1)] at h
  obtain ⟨s₁, hR₁, hK₁, h⟩ := seq_advance hR h
  rw [Parse.bind_ok] at h; obtain ⟨name, s₂, hn, h⟩ := h
  obtain ⟨nm, r₂, hnk, hs₂, rfl, hR₂⟩ := readPropertyName_inv hR₁ hn
  have hT₁ : s₁.target = T := hK₁.target_eq.trans hT
  have hnmok : Word.ok T (propertyName name) = true := propertyName_ok hnk (hT₁ ▸ hR₁.tok (by rw [hs₂]; simp)
    (by rcases hnk with h' | h' <;> rw [h'] <;> simp))
  obtain ⟨y, r₃, hs₃⟩ := hR₂.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₃)] at h
  obtain ⟨s₃, hR₃, hK₃, h⟩ := seq_advance hR₂ h
  obtain ⟨z, r₄, hs₄⟩ := hR₃.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₄)] at h
  obtain ⟨_, h⟩ := fail_inv h
  obtain ⟨hcol, h⟩ := pass_err (unexpected_refuses _ _) h
  have hzne : z.kind ≠ .eof := by simp [Token.isPunct] at hcol; rw [hcol]; simp
  rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₃ hs₄ hzne)), Parse.bind_eq (Parse.budget_eq _),
    Parse.bind_ok] at h
  obtain ⟨ty, s₅, hty, h⟩ := h
  obtain ⟨htwo, hR₅, hK₅⟩ := (types_give T _).1 _ _ _ (hR₃.past hs₄ (hR₃.more hs₄ hzne))
    (hK₃.target_eq.trans hT₁) hty
  have htw := both_left htwo
  have hK : Kept s s₅ := hK₁.trans ((Kept.past _ _ _).trans (hK₃.trans ((Kept.past _ _ _).trans hK₅)))
  obtain ⟨w, r₆, hs₆⟩ := hR₅.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₆)] at h
  by_cases hsep : (w.isPunct ";" || w.isPunct ",") = true
  · have hwne : w.kind ≠ .eof := by
      simp only [Bool.or_eq_true, Token.isPunct, beq_iff_eq] at hsep; rcases hsep with h' | h' <;> rw [h'] <;> simp
    rw [if_pos hsep, Parse.bind_eq (Parse.discard_eq (advance_past hR₅ hs₆ hwne)),
      Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR₅.past hs₆ (hR₅.more hs₆ hwne), hK.trans (Kept.past _ _ _), htw,
      Field.wordsOK _ hnmok (both_right htwo)⟩
  · rw [if_neg hsep] at h
    obtain ⟨_, h⟩ := fail_err (unexpected_refuses _ _) h
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR₅, hK, htw, Field.wordsOK _ hnmok (both_right htwo)⟩

theorem parseEnumMember_wf {T : Edition} :
    GivesW T (fun m : EnumMember => WordsOK T m.words) Parse.parseEnumMember := by
  intro s m s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseEnumMember] at h
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_ok] at h
  obtain ⟨name, s₁, hn, h⟩ := h
  obtain ⟨nm, r₁, hnk, hs₁, rfl, hR₁⟩ := readPropertyName_inv hR hn
  have hnmok : Word.ok T (propertyName name) = true := propertyName_ok hnk (hT ▸ hR.tok (by rw [hs₁]; simp)
    (by rcases hnk with h' | h' <;> rw [h'] <;> simp))
  obtain ⟨y, r₂, hs₂⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
  obtain ⟨hy, h⟩ := pass_err (refuseEnumMember_refuses _) h
  have hyne : y.kind ≠ .eof := by simp [Token.isPunct] at hy; rw [hy]; simp
  rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hs₂ hyne))] at h
  have hR₂ := hR₁.past hs₂ (hR₁.more hs₂ hyne)
  obtain ⟨z, r₃, hs₃⟩ := hR₂.cons
  rw [Parse.bind_ok] at h
  obtain ⟨v, s₃, hv, h⟩ := h
  obtain ⟨rfl, hpast⟩ := advance_inv hR₂ hs₃ hv
  generalize hk : v.kind = k at h
  cases k
  all_goals first
    | (simp only at h
       obtain ⟨_, _, he⟩ := refuseEnumMember_refuses (α := EnumMember) v s₃
       rw [he] at h; cases h)
    | skip
  rename_i value
  simp only at h
  have hzne : v.kind ≠ .eof := by rw [hk]; simp
  obtain ⟨rfl, hR₃⟩ := hpast hzne
  have hvok : Word.ok T [.string value] = true := by
    have := hR₂.tok (x := v) (by rw [hs₃]; simp) hzne
    rw [hk] at this
    simpa [past, hT] using this
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  obtain ⟨w, r₄, hs₄⟩ := hR₃.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₄)] at h
  have hK : Kept s (past (past (past s nm r₁) y r₂) v r₃) :=
    (Kept.past _ _ _).trans ((Kept.past _ _ _).trans (Kept.past _ _ _))
  by_cases hsep : w.isPunct "," = true
  · have hwne : w.kind ≠ .eof := by simp [Token.isPunct] at hsep; rw [hsep]; simp
    rw [if_pos hsep, Parse.bind_eq (Parse.discard_eq (advance_past hR₃ hs₄ hwne))] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR₃.past hs₄ (hR₃.more hs₄ hwne), hK.trans (Kept.past _ _ _), EnumMember.wordsOK _ hnmok hvok⟩
  · rw [if_neg hsep] at h
    obtain ⟨_, h⟩ := fail_err (unexpected_refuses _ _) h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR₃, hK, EnumMember.wordsOK _ hnmok hvok⟩

/-- `parseBlock` gives a block. -/
theorem parseBlock_block {n : Nat} {s s' : ParseState} {st : Stmt} (h : Parse.parseBlock n s = .ok st s') :
    st.isBlock = true := by
  cases n with
  | zero => simp only [Parse.parseBlock] at h; exact absurd h (outOfFuel_ne_ok _ _ _)
  | succ m =>
    simp only [Parse.parseBlock] at h
    rw [Parse.bind_ok] at h; obtain ⟨_, _, _, h⟩ := h
    rw [Parse.bind_ok] at h; obtain ⟨_, _, _, h⟩ := h
    rw [Parse.bind_ok] at h; obtain ⟨_, _, _, h⟩ := h
    rw [Parse.bind_ok] at h; obtain ⟨_, _, _, h⟩ := h
    rw [Parse.bind_ok] at h; obtain ⟨_, _, _, h⟩ := h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    rfl

/-- What a parser of declarations gives at the top of a module, outside every
function and loop: a well-formed declaration. -/
def GivesD (T : Edition) (p : ParseM Decl) : Prop :=
  ∀ s d s', Ready s → s.target = T → s.inFunction = false → s.loopDepth = 0 → p s = .ok d s' →
    Ready s' ∧ Kept s s' ∧ d.wf T = true ∧ DeclOK T d

/-- One step of the loop over the type parameters of a function keeps names
that `typeName` allows and that lex back. -/
theorem typeParamStep_inv {T : Edition} {s₀ s s' : ParseState} {a a' : Array String} {b : Bool}
    (hT : s₀.target = T)
    (hI : Ready s ∧ Kept s₀ s ∧ ∀ n ∈ a.toList, typeName n = true ∧ Word.ok T (identWord n) = true)
    (h : Parse.typeParamStep a s = .ok (a', b) s') :
    Ready s' ∧ Kept s₀ s' ∧ ∀ n ∈ a'.toList, typeName n = true ∧ Word.ok T (identWord n) = true := by
  obtain ⟨hR, hK, ha⟩ := hI
  simp only [Parse.typeParamStep] at h
  rw [Parse.bind_ok] at h; obtain ⟨t, s₁, hadv, h⟩ := h
  obtain ⟨x, r, hs⟩ := hR.cons
  obtain ⟨rfl, hpast⟩ := advance_inv hR hs hadv
  generalize hk : t.kind = k at h
  cases k with
  | ident name =>
    simp only at h
    have hne : t.kind ≠ .eof := by rw [hk]; simp
    obtain ⟨rfl, hR₁⟩ := hpast hne
    have hok : Word.ok T (identWord name) = true := by
      have := hR.tok (x := t) (by simp [hs]) hne
      rw [hK.target_eq, hT] at this
      simpa [identWord, hk] using this
    obtain ⟨hn, h⟩ := fail_inv h
    have htn : typeName name = true := by simpa [typeName] using hn
    have hK₁ : Kept s₀ (past s t r) := hK.trans (Kept.past _ _ _)
    rw [Parse.bind_eq (peek_eq' _)] at h
    obtain ⟨_, h⟩ := fail_inv h
    obtain ⟨_, h⟩ := fail_inv h
    have hnames : ∀ n ∈ (a.push name).toList, typeName n = true ∧ Word.ok T (identWord n) = true := by
      intro n hn'
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hn'
      rcases hn' with hn' | rfl
      · exact ha n hn'
      · exact ⟨htn, hok⟩
    split at h
    · simp only [Parse.pure_ok] at h
      obtain ⟨h1, rfl⟩ := h
      cases h1
      exact ⟨hR₁, hK₁, hnames⟩
    · rw [Parse.pure_bind, Parse.bind_ok] at h; obtain ⟨_, s₂, hd, h⟩ := h
      obtain ⟨hR₂, hK₂⟩ := discard_advance_ready hR₁ hd
      simp only [Parse.pure_ok] at h
      obtain ⟨h1, rfl⟩ := h
      cases h1
      exact ⟨hR₂, hK₁.trans hK₂, hnames⟩
  | _ => simp at h

/-- `parseTypeParams` gives names that `typeName` allows and that lex back. -/
theorem parseTypeParams_wf {T : Edition} {s s' : ParseState} {tps : List String} (hR : Ready s)
    (hT : s.target = T) (h : Parse.parseTypeParams s = .ok tps s') :
    Ready s' ∧ Kept s s' ∧ (∀ n ∈ tps, typeName n = true) ∧ WordsOK T (typeParamWords tps) := by
  simp only [Parse.parseTypeParams] at h
  rw [Parse.bind_eq (peek_eq' _)] at h
  split at h
  · rw [Parse.pure_bind, Parse.bind_ok] at h; obtain ⟨_, s₁, hadv, h⟩ := h
    obtain ⟨hR₁, hK₁⟩ := discard_advance_ready hR hadv
    rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
    obtain ⟨names, s₂, hit, h⟩ := h
    obtain ⟨⟨hR₂, hK₂, hn⟩, -⟩ := iterate_inv
      (I := fun a st => Ready st ∧ Kept s₁ st ∧ ∀ n ∈ a.toList, typeName n = true ∧ Word.ok T (identWord n) = true)
      (fun _ _ _ _ _ hI hst => typeParamStep_inv (hK₁.target_eq.trans hT) hI hst) _ #[] _ names s₂
      ⟨hR₁, Kept.refl _, by simp⟩ hit
    rw [Parse.bind_ok] at h; obtain ⟨gt, s₃, hgt, h⟩ := h
    obtain ⟨_, r, _, rfl, hR₃⟩ := expectPunct_inv hR₂ hgt
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨hR₃, hK₁.trans (hK₂.trans (Kept.past _ _ _)), fun n hn' => (hn n hn').1, ?_⟩
    cases hl : names.toList with
    | nil => exact WordsOK.nil
    | cons n more =>
      simp only [typeParamWords]
      exact wordsOK_enclose (by decide) (by decide) fun x hx => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
        exact WordsOK.word (hn k (by rw [hl]; exact hk)).2
  · simp only [Parse.pure_ok] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR, Kept.refl _, by simp, WordsOK.nil⟩

theorem parseFunction_wf {T : Edition} (start : Pos) (exported : Bool) :
    GivesD T (Parse.parseFunction start exported) := by
  intro s d s' hR hT hF hL h
  simp only [Parse.parseFunction] at h
  rw [Parse.bind_ok] at h; obtain ⟨_, s₁, hadv, h⟩ := h
  obtain ⟨hR₁, hK₁⟩ := discard_advance_ready hR hadv
  obtain ⟨x, r, hs⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  obtain ⟨_, h⟩ := fail_inv h
  rw [Parse.bind_ok] at h; obtain ⟨name, s₂, hn, h⟩ := h
  have hT₁ : s₁.target = T := hK₁.target_eq.trans hT
  have hnok := readName_words hR₁ hT₁ hn
  obtain ⟨tn, r₂, _, hnr, _, rfl, hR₂⟩ := readName_inv hR₁ hn
  rw [Parse.bind_ok] at h; obtain ⟨tps, s₂', htp, h⟩ := h
  obtain ⟨hR₂', hK₂', htpn, htpw⟩ := parseTypeParams_wf hR₂ hT₁ htp
  rw [Parse.bind_ok] at h; obtain ⟨lp, s₃, hlp, h⟩ := h
  obtain ⟨_, r₄, _, rfl, hR₃⟩ := expectPunct_inv hR₂' hlp
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
  obtain ⟨params, s₄, hps, h⟩ := h
  obtain ⟨hR₄, hK₄, hpw⟩ := (iterate_inv
    (I := fun a st => Ready st ∧ Kept (past s₂' lp r₄) st ∧
      ∀ x ∈ a.toList, Param.wf x = true ∧ WordsOK T x.words)
    (fun _ _ _ _ _ hI hst => listStep_wf parseParam_wf
      (fun _ _ _ h' => by simp only [Parse.pure_ok] at h'; exact h'.2.symm) (s₀ := past s₂' lp r₄)
      (hK₂'.target_eq.trans hT₁) hI hst)
    _ #[] _ params s₄ ⟨hR₃, Kept.refl _, by simp⟩ hps).1
  rw [Parse.bind_ok] at h; obtain ⟨rp, s₅, hrp, h⟩ := h
  obtain ⟨_, r₅, _, rfl, hR₅⟩ := expectPunct_inv hR₄ hrp
  have hK₅ : Kept s (past s₄ rp r₅) :=
    hK₁.trans ((Kept.past _ _ _).trans (hK₂'.trans ((Kept.past _ _ _).trans (hK₄.trans (Kept.past _ _ _)))))
  obtain ⟨z, r₆, hs₆⟩ := hR₅.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₆)] at h
  by_cases hcol : z.isPunct ":" = true
  · have hzne : z.kind ≠ .eof := by simp [Token.isPunct] at hcol; rw [hcol]; simp
    rw [if_pos hcol, Parse.bind_eq (Parse.discard_eq (advance_past hR₅ hs₆ hzne)), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_ok] at h
    obtain ⟨ty, s₆, hty, h⟩ := h
    obtain ⟨htwo, hR₆, hK₆'⟩ := (types_give T _).1 _ _ _ (hR₅.past hs₆ (hR₅.more hs₆ hzne))
      (hK₅.target_eq.trans hT) hty
    have htw := both_left htwo
    have hK₆ : Kept s s₆ := hK₅.trans ((Kept.past _ _ _).trans hK₆')
    rw [Parse.pure_bind] at h
    obtain ⟨w, r₇, hs₇⟩ := hR₆.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₇)] at h
    obtain ⟨_, h⟩ := pass_err (unexpected_refuses _ _) h
    rw [Parse.bind_eq (Parse.modify_eq _ _), Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
    obtain ⟨body, s₈, hb, h⟩ := h
    have hR₇ : Ready { s₆ with inFunction := true } := ⟨hR₆.1, hR₆.2.1, hR₆.2.2.1, hR₆.2.2.2⟩
    obtain ⟨hR₈, hK₈, hbw, _, _, hbok⟩ := (stmts_give T _).2.2.1 _ _ _ hR₇ (by rw [show
      ({ s₆ with inFunction := true } : ParseState).target = s₆.target from rfl, hK₆.target_eq, hT]) hb
    rw [Parse.bind_eq (Parse.modify_eq _ _), Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨⟨hR₈.1, hR₈.2.1, hR₈.2.2.1, hR₈.2.2.2⟩,
      ⟨by rw [show ({ s₈ with inFunction := false } : ParseState).eof = s₈.eof from rfl, hK₈.eof_eq]; exact hK₆.eof_eq,
        by simp [hF],
        by rw [show ({ s₈ with inFunction := false } : ParseState).loopDepth = s₈.loopDepth from rfl, hK₈.loopDepth_eq];
           exact hK₆.loopDepth_eq,
        by rw [show ({ s₈ with inFunction := false } : ParseState).target = s₈.target from rfl, hK₈.target_eq];
           exact hK₆.target_eq⟩, ?_, DeclOK.function hnok htpw (fun p hp => (hpw p (by simpa using hp)).2)
        (fun t ht => by simp at ht; subst ht; exact both_right htwo) hbok⟩
    have hld : s₆.loopDepth = 0 := hK₆.loopDepth_eq.trans hL
    simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨by simpa [exprName] using hnr, htpn⟩, fun x hx => (hpw x (by simpa using hx)).1⟩, by simpa using htw⟩,
      parseBlock_block hb⟩, ?_⟩
    simpa [hld] using hbw
  · rw [if_neg hcol, Parse.pure_bind] at h
    have hR₆ := hR₅
    have hK₆ := hK₅
    obtain ⟨w, r₇, hs₇⟩ := hR₆.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₇)] at h
    obtain ⟨_, h⟩ := pass_err (unexpected_refuses _ _) h
    rw [Parse.bind_eq (Parse.modify_eq _ _), Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
    obtain ⟨body, s₈, hb, h⟩ := h
    have hR₇ : Ready { (past s₄ rp r₅) with inFunction := true } := ⟨hR₆.1, hR₆.2.1, hR₆.2.2.1, hR₆.2.2.2⟩
    obtain ⟨hR₈, hK₈, hbw, _, _, hbok⟩ := (stmts_give T _).2.2.1 _ _ _ hR₇ (by rw [show
      ({ (past s₄ rp r₅) with inFunction := true } : ParseState).target = (past s₄ rp r₅).target from rfl, hK₆.target_eq, hT]) hb
    rw [Parse.bind_eq (Parse.modify_eq _ _), Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨⟨hR₈.1, hR₈.2.1, hR₈.2.2.1, hR₈.2.2.2⟩,
      ⟨by rw [show ({ s₈ with inFunction := false } : ParseState).eof = s₈.eof from rfl, hK₈.eof_eq]; exact hK₆.eof_eq,
        by simp [hF],
        by rw [show ({ s₈ with inFunction := false } : ParseState).loopDepth = s₈.loopDepth from rfl, hK₈.loopDepth_eq];
           exact hK₆.loopDepth_eq,
        by rw [show ({ s₈ with inFunction := false } : ParseState).target = s₈.target from rfl, hK₈.target_eq];
           exact hK₆.target_eq⟩, ?_, DeclOK.function hnok htpw (fun p hp => (hpw p (by simpa using hp)).2)
        (fun t ht => by simp at ht) hbok⟩
    have hld : s₄.loopDepth = 0 := hK₆.loopDepth_eq.trans hL
    simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨by simpa [exprName] using hnr, htpn⟩, fun x hx => (hpw x (by simpa using hx)).1⟩, by simp⟩,
      parseBlock_block hb⟩, ?_⟩
    simpa [hld] using hbw

theorem parseInterface_wf {T : Edition} (start : Pos) (exported : Bool) :
    GivesD T (Parse.parseInterface start exported) := by
  intro s d s' hR hT hF hL h
  simp only [Parse.parseInterface] at h
  rw [Parse.bind_ok] at h; obtain ⟨_, s₁, hadv, h⟩ := h
  obtain ⟨hR₁, hK₁⟩ := discard_advance_ready hR hadv
  rw [Parse.bind_ok] at h; obtain ⟨name, s₂, hn, h⟩ := h
  have hT₁ : s₁.target = T := hK₁.target_eq.trans hT
  have hnok := readName_words hR₁ hT₁ hn
  obtain ⟨tn, r₂, _, hnr, _, rfl, hR₂⟩ := readName_inv hR₁ hn
  rw [Parse.bind_ok] at h; obtain ⟨tps, s₂', htp, h⟩ := h
  obtain ⟨hR₂', hK₂', htpn, htpw⟩ := parseTypeParams_wf hR₂ hT₁ htp
  obtain ⟨y, r₃, hs₃⟩ := hR₂'.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₃)] at h
  obtain ⟨_, h⟩ := fail_inv h
  rw [Parse.bind_ok] at h; obtain ⟨lb, s₃, hlb, h⟩ := h
  obtain ⟨_, r₄, _, rfl, hR₃⟩ := expectPunct_inv hR₂' hlb
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
  obtain ⟨fields, s₄, hfs, h⟩ := h
  obtain ⟨hR₄, hK₄, hfw⟩ := (iterate_inv
    (I := fun a st => Ready st ∧ Kept (past s₂' lb r₄) st ∧
      ∀ x ∈ a.toList, x.type.wf = true ∧ WordsOK T x.words)
    (fun _ _ _ _ _ hI hst => blockStep_wf parseField_wf (s₀ := past s₂' lb r₄) (hK₂'.target_eq.trans hT₁) hI hst)
    _ #[] _ fields s₄ ⟨hR₃, Kept.refl _, by simp⟩ hfs).1
  rw [Parse.bind_ok] at h; obtain ⟨rb, s₅, hrb, h⟩ := h
  obtain ⟨_, r₅, _, rfl, hR₅⟩ := expectPunct_inv hR₄ hrb
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  refine ⟨hR₅, hK₁.trans ((Kept.past _ _ _).trans (hK₂'.trans ((Kept.past _ _ _).trans (hK₄.trans
    (Kept.past _ _ _))))), ?_, DeclOK.interface hnok htpw (fun f hf => (hfw f (by simpa using hf)).2)⟩
  simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨by simpa [exprName] using hnr, htpn⟩, fun x hx => (hfw x (by simpa using hx)).1⟩

theorem parseTypeAlias_wf {T : Edition} (start : Pos) (exported : Bool) :
    GivesD T (Parse.parseTypeAlias start exported) := by
  intro s d s' hR hT hF hL h
  simp only [Parse.parseTypeAlias] at h
  rw [Parse.bind_ok] at h; obtain ⟨_, s₁, hadv, h⟩ := h
  obtain ⟨hR₁, hK₁⟩ := discard_advance_ready hR hadv
  rw [Parse.bind_ok] at h; obtain ⟨name, s₂, hn, h⟩ := h
  have hT₁ : s₁.target = T := hK₁.target_eq.trans hT
  have hnok := readName_words hR₁ hT₁ hn
  obtain ⟨tn, r₂, _, hnr, _, rfl, hR₂⟩ := readName_inv hR₁ hn
  rw [Parse.bind_ok] at h; obtain ⟨tps, s₂', htp, h⟩ := h
  obtain ⟨hR₂', hK₂', htpn, htpw⟩ := parseTypeParams_wf hR₂ hT₁ htp
  rw [Parse.bind_ok] at h; obtain ⟨eq, s₃, heq, h⟩ := h
  obtain ⟨_, r₄, _, rfl, hR₃⟩ := expectPunct_inv hR₂' heq
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
  obtain ⟨ty, s₄, hty, h⟩ := h
  obtain ⟨htwo, hR₄, hK₄⟩ := (types_give T _).1 _ _ _ hR₃ (hK₂'.target_eq.trans hT₁) hty
  have htw := both_left htwo
  rw [Parse.bind_ok] at h; obtain ⟨_, s₅, hend, h⟩ := h
  obtain ⟨hR₅, hK₅⟩ := endStatement_inv hR₄ hend
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  refine ⟨hR₅, hK₁.trans ((Kept.past _ _ _).trans (hK₂'.trans ((Kept.past _ _ _).trans (hK₄.trans hK₅)))), ?_,
    DeclOK.typeAlias hnok htpw (both_right htwo)⟩
  simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨by simpa [exprName] using hnr, htpn⟩, htw⟩

theorem parseEnum_wf {T : Edition} (start : Pos) (exported : Bool) :
    GivesD T (Parse.parseEnum start exported) := by
  intro s d s' hR hT hF hL h
  simp only [Parse.parseEnum] at h
  rw [Parse.bind_ok] at h; obtain ⟨_, s₁, hadv, h⟩ := h
  obtain ⟨hR₁, hK₁⟩ := discard_advance_ready hR hadv
  rw [Parse.bind_ok] at h; obtain ⟨name, s₂, hn, h⟩ := h
  have hT₁ : s₁.target = T := hK₁.target_eq.trans hT
  have hnok := readName_words hR₁ hT₁ hn
  obtain ⟨tn, r₂, _, hnr, _, rfl, hR₂⟩ := readName_inv hR₁ hn
  rw [Parse.bind_ok] at h; obtain ⟨lb, s₃, hlb, h⟩ := h
  obtain ⟨_, r₄, _, rfl, hR₃⟩ := expectPunct_inv hR₂ hlb
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
  obtain ⟨members, s₄, hms, h⟩ := h
  obtain ⟨hR₄, hK₄, hmw⟩ := (iterate_inv
    (I := fun a st => Ready st ∧ Kept (past (past s₁ tn r₂) lb r₄) st ∧ ∀ x ∈ a.toList, WordsOK T x.words)
    (fun _ _ _ _ _ hI hst => blockStep_wf parseEnumMember_wf (s₀ := past (past s₁ tn r₂) lb r₄) hT₁ hI hst)
    _ #[] _ members s₄ ⟨hR₃, Kept.refl _, by simp⟩ hms).1
  rw [Parse.bind_ok] at h; obtain ⟨rb, s₅, hrb, h⟩ := h
  obtain ⟨_, r₅, _, rfl, hR₅⟩ := expectPunct_inv hR₄ hrb
  rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  refine ⟨hR₅, hK₁.trans ((Kept.past _ _ _).trans ((Kept.past _ _ _).trans (hK₄.trans (Kept.past _ _ _)))), ?_,
    DeclOK.enum hnok (fun m hm => hmw m (by simpa using hm))⟩
  simpa [Decl.wf, exprName] using hnr

theorem importStep_wf {T : Edition} {ct : Bool} {s₀ : ParseState} (hT : s₀.target = T)
    {names names' : Array ImportName} {b : Bool} {s s' : ParseState}
    (hI : Ready s ∧ Kept s₀ s ∧ ∀ n ∈ names.toList, exprName n.name = true ∧ WordsOK T n.words)
    (h : Parse.importStep ct names s = .ok (names', b) s') :
    Ready s' ∧ Kept s₀ s' ∧ ∀ n ∈ names'.toList, exprName n.name = true ∧ WordsOK T n.words := by
  obtain ⟨hR, hK, hall⟩ := hI
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.importStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : x.isPunct "}" = true
  · rw [if_pos hc] at h; simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR, hK, hall⟩
  rw [if_neg hc, Parse.pure_bind, Parse.bind_eq (Parse.peekAt_rest s 1)] at h
  obtain ⟨_, h⟩ := fail_inv h
  obtain ⟨s₁, hR₁, hK₁, h⟩ := seq_advance hR h
  obtain ⟨y, r₁, hs₁⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₁), Parse.bind_ok] at h
  obtain ⟨name, s₂, hn, h⟩ := h
  have hnok := readName_words hR₁ (hK₁.target_eq.trans (hK.target_eq.trans hT)) hn
  obtain ⟨tn, r₂, _, hnr, _, rfl, hR₂⟩ := readName_inv hR₁ hn
  obtain ⟨z, r₃, hs₃⟩ := hR₂.cons
  rw [Parse.bind_eq (Parse.peek_eq hs₃)] at h
  by_cases has : z.isIdent "as" = true
  · rw [if_pos has, Parse.bind_eq (Parse.peek_eq hs₃)] at h
    exact absurd h ((refuseImport_refuses _).bind _ _ _ _)
  rw [if_neg has, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₃)] at h
  have hall' : ∀ n ∈ (names.push { span := y.span, typeOnly := ct || x.isIdent "type" &&
      (s.rest[1]?.getD s.eof).isAnyIdent, name := name }).toList, exprName n.name = true ∧ WordsOK T n.words := by
    intro n hn'
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hn'
    rcases hn' with hn' | rfl
    · exact hall n hn'
    · exact ⟨by simpa [exprName] using hnr, ImportName.wordsOK _ hnok⟩
  have hK₂ : Kept s₀ (past s₁ tn r₂) := hK.trans (hK₁.trans (Kept.past _ _ _))
  by_cases hcm : z.isPunct "," = true
  · have hzne : z.kind ≠ .eof := by simp [Token.isPunct] at hcm; rw [hcm]; simp
    rw [if_pos hcm, Parse.bind_eq (Parse.discard_eq (advance_past hR₂ hs₃ hzne))] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR₂.past hs₃ (hR₂.more hs₃ hzne), hK₂.trans (Kept.past _ _ _), hall'⟩
  rw [if_neg hcm] at h
  obtain ⟨_, h⟩ := fail_err (unexpected_refuses _ _) h
  simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
  exact ⟨hR₂, hK₂, hall'⟩

theorem parseImport_wf {T : Edition} (start : Pos) : GivesD T (Parse.parseImport start) := by
  intro s d s' hR hT hF hL h
  simp only [Parse.parseImport] at h
  rw [Parse.bind_ok] at h; obtain ⟨_, s₁, hadv, h⟩ := h
  obtain ⟨hR₁, hK₁⟩ := discard_advance_ready hR hadv
  obtain ⟨x, r, hs⟩ := hR₁.cons
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.peekAt_rest s₁ 1)] at h
  by_cases hct : (x.isIdent "type" && (s₁.rest[1]?.getD s₁.eof).isPunct "{") = true
  · have hxne : x.kind ≠ .eof := by
      simp only [Bool.and_eq_true, Token.isIdent, beq_iff_eq] at hct; rw [hct.1]; simp
    have hRp := hR₁.past hs (hR₁.more hs hxne)
    have hKp : Kept s (past s₁ x r) := hK₁.trans (Kept.past _ _ _)
    rw [if_pos hct, Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hs hxne)), Parse.pure_bind] at h
    obtain ⟨y, r₂, hs₂⟩ := hRp.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
    obtain ⟨hlb, h⟩ := pass_err (refuseImport_refuses _) h
    have hyne : y.kind ≠ .eof := by simp [Token.isPunct] at hlb; rw [hlb]; simp
    rw [Parse.bind_eq (Parse.discard_eq (advance_past hRp hs₂ hyne)), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_ok] at h
    obtain ⟨names, s₃, hns, h⟩ := h
    obtain ⟨hR₃, hK₃, hnw⟩ := (iterate_inv
      (I := fun a st => Ready st ∧ Kept (past (past s₁ x r) y r₂) st ∧
        ∀ n ∈ a.toList, exprName n.name = true ∧ WordsOK T n.words)
      (fun _ _ _ _ _ hI hst => importStep_wf (s₀ := past (past s₁ x r) y r₂) (hK₁.target_eq.trans hT) hI hst) _ #[]
      _ names s₃
      ⟨hRp.past hs₂ (hRp.more hs₂ hyne), Kept.refl _, by simp⟩ hns).1
    rw [Parse.bind_ok] at h; obtain ⟨close, s₄, hcl, h⟩ := h
    obtain ⟨_, r₄, _, rfl, hR₄⟩ := expectPunct_inv hR₃ hcl
    obtain ⟨hne, h⟩ := fail_inv h
    obtain ⟨z, r₅, hs₅⟩ := hR₄.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₅)] at h
    obtain ⟨hfrom, h⟩ := pass_err (unexpected_refuses _ _) h
    have hzne : z.kind ≠ .eof := by simp [Token.isIdent] at hfrom; rw [hfrom]; simp
    have hR₅ := hR₄.past hs₅ (hR₄.more hs₅ hzne)
    rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₄ hs₅ hzne)), Parse.bind_ok] at h
    obtain ⟨t, s₆, hadv2, h⟩ := h
    obtain ⟨w, r₆, hs₆⟩ := hR₅.cons
    obtain ⟨rfl, hpast⟩ := advance_inv hR₅ hs₆ hadv2
    generalize hk : t.kind = k at h hpast
    cases k with
    | string source =>
      obtain ⟨rfl, hR₆⟩ := hpast (by simp)
      simp only at h
      rw [Parse.bind_ok] at h; obtain ⟨_, s₇, hend, h⟩ := h
      obtain ⟨hR₇, hK₇⟩ := endStatement_inv hR₆ hend
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨hR₇, hKp.trans ((Kept.past _ _ _).trans (hK₃.trans ((Kept.past _ _ _).trans
        ((Kept.past _ _ _).trans ((Kept.past _ _ _).trans hK₇))))), ?_,
        DeclOK.import (fun n hn => (hnw n (by simpa using hn)).2)⟩
      simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
      exact ⟨by simpa using hne, fun n hn => (hnw n (by simpa using hn)).1⟩
    | _ => simp at h
  · rw [if_neg hct, Parse.pure_bind] at h
    obtain ⟨y, r₂, hs₂⟩ := hR₁.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₂)] at h
    obtain ⟨hlb, h⟩ := pass_err (refuseImport_refuses _) h
    have hyne : y.kind ≠ .eof := by simp [Token.isPunct] at hlb; rw [hlb]; simp
    rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hs₂ hyne)), Parse.bind_eq (Parse.budget_eq _),
      Parse.bind_ok] at h
    obtain ⟨names, s₃, hns, h⟩ := h
    obtain ⟨hR₃, hK₃, hnw⟩ := (iterate_inv
      (I := fun a st => Ready st ∧ Kept (past s₁ y r₂) st ∧
        ∀ n ∈ a.toList, exprName n.name = true ∧ WordsOK T n.words)
      (fun _ _ _ _ _ hI hst => importStep_wf (s₀ := past s₁ y r₂) (hK₁.target_eq.trans hT) hI hst) _ #[] _ names s₃
      ⟨hR₁.past hs₂ (hR₁.more hs₂ hyne), Kept.refl _, by simp⟩ hns).1
    rw [Parse.bind_ok] at h; obtain ⟨close, s₄, hcl, h⟩ := h
    obtain ⟨_, r₄, _, rfl, hR₄⟩ := expectPunct_inv hR₃ hcl
    obtain ⟨hne, h⟩ := fail_inv h
    obtain ⟨z, r₅, hs₅⟩ := hR₄.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₅)] at h
    obtain ⟨hfrom, h⟩ := pass_err (unexpected_refuses _ _) h
    have hzne : z.kind ≠ .eof := by simp [Token.isIdent] at hfrom; rw [hfrom]; simp
    have hR₅ := hR₄.past hs₅ (hR₄.more hs₅ hzne)
    rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₄ hs₅ hzne)), Parse.bind_ok] at h
    obtain ⟨t, s₆, hadv2, h⟩ := h
    obtain ⟨w, r₆, hs₆⟩ := hR₅.cons
    obtain ⟨rfl, hpast⟩ := advance_inv hR₅ hs₆ hadv2
    generalize hk : t.kind = k at h hpast
    cases k with
    | string source =>
      obtain ⟨rfl, hR₆⟩ := hpast (by simp)
      simp only at h
      rw [Parse.bind_ok] at h; obtain ⟨_, s₇, hend, h⟩ := h
      obtain ⟨hR₇, hK₇⟩ := endStatement_inv hR₆ hend
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨hR₇, hK₁.trans ((Kept.past _ _ _).trans (hK₃.trans ((Kept.past _ _ _).trans
        ((Kept.past _ _ _).trans ((Kept.past _ _ _).trans hK₇))))), ?_,
        DeclOK.import (fun n hn => (hnw n (by simpa using hn)).2)⟩
      simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
      exact ⟨by simpa using hne, fun n hn => (hnw n (by simpa using hn)).1⟩
    | _ => simp at h

theorem parseExportList_wf {T : Edition} (start : Pos) : GivesD T (Parse.parseExportList start) := by
  intro s d s' hR hT hF hL h
  simp only [Parse.parseExportList] at h
  obtain ⟨x, r, hs⟩ := hR.cons
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hct : x.isIdent "type" = true
  · have hxne : x.kind ≠ .eof := by simp only [Token.isIdent, beq_iff_eq] at hct; rw [hct]; simp
    have HR := hR.past hs (hR.more hs hxne)
    have HK : Kept s (past s x r) := Kept.past _ _ _
    rw [if_pos hct, Parse.bind_eq (Parse.discard_eq (advance_past hR hs hxne)), Parse.pure_bind] at h
    rw [Parse.bind_ok] at h; obtain ⟨_, s₂, hadv, h⟩ := h
    obtain ⟨hR₂, hK₂⟩ := discard_advance_ready HR hadv
    rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
    obtain ⟨names, s₃, hns, h⟩ := h
    obtain ⟨hR₃, hK₃, hnw⟩ := (iterate_inv
      (I := fun a st => Ready st ∧ Kept s₂ st ∧ ∀ n ∈ a.toList, exprName n.name = true ∧ WordsOK T n.words)
      (fun _ _ _ _ _ hI hst => importStep_wf (s₀ := s₂) (hK₂.target_eq.trans (HK.target_eq.trans hT)) hI hst) _ #[]
      _ names s₃ ⟨hR₂, Kept.refl _, by simp⟩ hns).1
    rw [Parse.bind_ok] at h; obtain ⟨close, s₄, hcl, h⟩ := h
    obtain ⟨_, r₄, _, rfl, hR₄⟩ := expectPunct_inv hR₃ hcl
    obtain ⟨hne, h⟩ := fail_inv h
    have hwf : ∀ sp src, (Decl.exports sp names.toList src).wf T = true := by
      intro _ _
      simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
      exact ⟨by simpa using hne, fun n hn => (hnw n (by simpa using hn)).1⟩
    have hok : ∀ sp' src', DeclOK T (.exports sp' names.toList src') :=
      fun _ _ => DeclOK.exports (fun n hn => (hnw n (by simpa using hn)).2)
    have hKK : Kept s (past s₃ close r₄) := HK.trans (hK₂.trans (hK₃.trans (Kept.past _ _ _)))
    obtain ⟨z, r₅, hs₅⟩ := hR₄.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₅)] at h
    by_cases hfr : (!z.isIdent "from") = true
    · rw [if_pos hfr, Parse.bind_ok] at h; obtain ⟨_, s₇, hend, h⟩ := h
      obtain ⟨hR₇, hK₇⟩ := endStatement_inv hR₄ hend
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨hR₇, hKK.trans hK₇, hwf _ _, hok _ _⟩
    · rw [if_neg hfr, Parse.pure_bind] at h
      have hzne : z.kind ≠ .eof := by simp [Token.isIdent] at hfr; rw [hfr]; simp
      have hR₅ := hR₄.past hs₅ (hR₄.more hs₅ hzne)
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₄ hs₅ hzne)), Parse.bind_ok] at h
      obtain ⟨t, s₆, hadv2, h⟩ := h
      obtain ⟨w, r₆, hs₆⟩ := hR₅.cons
      obtain ⟨rfl, hpast⟩ := advance_inv hR₅ hs₆ hadv2
      generalize hk : t.kind = k at h hpast
      cases k with
      | string source =>
        obtain ⟨rfl, hR₆⟩ := hpast (by simp)
        simp only at h
        rw [Parse.bind_ok] at h; obtain ⟨_, s₇, hend, h⟩ := h
        obtain ⟨hR₇, hK₇⟩ := endStatement_inv hR₆ hend
        rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨hR₇, hKK.trans ((Kept.past _ _ _).trans ((Kept.past _ _ _).trans hK₇)),
          hwf _ _, hok _ _⟩
      | _ => simp at h
  · rw [if_neg hct, Parse.pure_bind] at h
    have HR := hR
    have HK : Kept s s := Kept.refl _
    rw [Parse.bind_ok] at h; obtain ⟨_, s₂, hadv, h⟩ := h
    obtain ⟨hR₂, hK₂⟩ := discard_advance_ready HR hadv
    rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
    obtain ⟨names, s₃, hns, h⟩ := h
    obtain ⟨hR₃, hK₃, hnw⟩ := (iterate_inv
      (I := fun a st => Ready st ∧ Kept s₂ st ∧ ∀ n ∈ a.toList, exprName n.name = true ∧ WordsOK T n.words)
      (fun _ _ _ _ _ hI hst => importStep_wf (s₀ := s₂) (hK₂.target_eq.trans (HK.target_eq.trans hT)) hI hst) _ #[]
      _ names s₃ ⟨hR₂, Kept.refl _, by simp⟩ hns).1
    rw [Parse.bind_ok] at h; obtain ⟨close, s₄, hcl, h⟩ := h
    obtain ⟨_, r₄, _, rfl, hR₄⟩ := expectPunct_inv hR₃ hcl
    obtain ⟨hne, h⟩ := fail_inv h
    have hwf : ∀ sp src, (Decl.exports sp names.toList src).wf T = true := by
      intro _ _
      simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
      exact ⟨by simpa using hne, fun n hn => (hnw n (by simpa using hn)).1⟩
    have hok : ∀ sp' src', DeclOK T (.exports sp' names.toList src') :=
      fun _ _ => DeclOK.exports (fun n hn => (hnw n (by simpa using hn)).2)
    have hKK : Kept s (past s₃ close r₄) := HK.trans (hK₂.trans (hK₃.trans (Kept.past _ _ _)))
    obtain ⟨z, r₅, hs₅⟩ := hR₄.cons
    rw [Parse.bind_eq (Parse.peek_eq hs₅)] at h
    by_cases hfr : (!z.isIdent "from") = true
    · rw [if_pos hfr, Parse.bind_ok] at h; obtain ⟨_, s₇, hend, h⟩ := h
      obtain ⟨hR₇, hK₇⟩ := endStatement_inv hR₄ hend
      rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
      simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨hR₇, hKK.trans hK₇, hwf _ _, hok _ _⟩
    · rw [if_neg hfr, Parse.pure_bind] at h
      have hzne : z.kind ≠ .eof := by simp [Token.isIdent] at hfr; rw [hfr]; simp
      have hR₅ := hR₄.past hs₅ (hR₄.more hs₅ hzne)
      rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₄ hs₅ hzne)), Parse.bind_ok] at h
      obtain ⟨t, s₆, hadv2, h⟩ := h
      obtain ⟨w, r₆, hs₆⟩ := hR₅.cons
      obtain ⟨rfl, hpast⟩ := advance_inv hR₅ hs₆ hadv2
      generalize hk : t.kind = k at h hpast
      cases k with
      | string source =>
        obtain ⟨rfl, hR₆⟩ := hpast (by simp)
        simp only at h
        rw [Parse.bind_ok] at h; obtain ⟨_, s₇, hend, h⟩ := h
        obtain ⟨hR₇, hK₇⟩ := endStatement_inv hR₆ hend
        rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨hR₇, hKK.trans ((Kept.past _ _ _).trans ((Kept.past _ _ _).trans hK₇)),
          hwf _ _, hok _ _⟩
      | _ => simp at h

theorem parseDecl_wf {T : Edition} : GivesD T Parse.parseDecl := by
  intro s d s' hR hT hF hL h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseDecl] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hi : x.isKeyword "import" = true
  · rw [if_pos hi, Parse.bind_ok] at h; obtain ⟨d', s₁, hd, h⟩ := h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact parseImport_wf _ _ _ _ hR hT hF hL hd
  rw [if_neg hi, Parse.pure_bind] at h
  obtain ⟨s₁, hR₁, hK₁, h⟩ := seq_advance hR h
  have hT₁ : s₁.target = T := hK₁.target_eq.trans hT
  have hF₁ : s₁.inFunction = false := hK₁.inFunction_eq.trans hF
  have hL₁ : s₁.loopDepth = 0 := hK₁.loopDepth_eq.trans hL
  rw [Parse.bind_eq (startsExportList_eq s₁)] at h
  split at h
  · rw [Parse.bind_ok] at h; obtain ⟨d', s₂, hd, h⟩ := h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hR₂, hK₂, hw, hok⟩ := parseExportList_wf _ _ _ _ hR₁ hT₁ hF₁ hL₁ hd
    exact ⟨hR₂, hK₁.trans hK₂, hw, hok⟩
  rw [Parse.pure_bind] at h
  obtain ⟨y, r₁, hs₁⟩ := hR₁.cons
  simp only [Parse.parseDeclBody] at h
  rw [Parse.bind_eq (Parse.peek_eq hs₁), Parse.bind_eq (Parse.peekAt_rest s₁ 1)] at h
  simp only [Parse.ite_state] at h
  split at h
  · obtain ⟨hR₂, hK₂, hw, hok⟩ := parseFunction_wf _ _ _ _ _ hR₁ hT₁ hF₁ hL₁ h; exact ⟨hR₂, hK₁.trans hK₂, hw, hok⟩
  split at h
  · obtain ⟨hR₂, hK₂, hw, hok⟩ := parseInterface_wf _ _ _ _ _ hR₁ hT₁ hF₁ hL₁ h; exact ⟨hR₂, hK₁.trans hK₂, hw, hok⟩
  split at h
  · obtain ⟨hR₂, hK₂, hw, hok⟩ := parseTypeAlias_wf _ _ _ _ _ hR₁ hT₁ hF₁ hL₁ h; exact ⟨hR₂, hK₁.trans hK₂, hw, hok⟩
  split at h
  · obtain ⟨hR₂, hK₂, hw, hok⟩ := parseEnum_wf _ _ _ _ _ hR₁ hT₁ hF₁ hL₁ h; exact ⟨hR₂, hK₁.trans hK₂, hw, hok⟩
  split at h
  · split at h
    rotate_left
    · exact absurd h (failAt_bind_ne_ok _ _ _ _ _ _)
    rename_i hcl
    rw [Parse.pure_bind] at h
    have hyne : y.kind ≠ .eof := by
      simp only [Bool.or_eq_true, Token.isKeyword, Token.isIdent, beq_iff_eq] at hcl
      rcases hcl with h' | h' <;> rw [h'] <;> simp
    rw [Parse.bind_ok] at h; obtain ⟨dd, s₂, hvd, h⟩ := h
    obtain ⟨hR₂, hK₂, hdw, hdok⟩ := parseVarDecl_inv hR₁ hT₁ hs₁ hyne hvd
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR₂, hK₁.trans hK₂, by simpa [Decl.wf] using hdw, DeclOK.exportedVar hdok⟩
  · rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h; obtain ⟨st, s₂, hst, h⟩ := h
    obtain ⟨hR₂, hK₂, hw, _, _, hok⟩ := (stmts_give T _).1 _ _ _ hR₁ hT₁ hst
    simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR₂, hK₁.trans hK₂, by simpa [Decl.wf, hF₁, hL₁] using hw, DeclOK.stmt hok⟩

theorem declStep_wf {T : Edition} {s₀ : ParseState} (hT : s₀.target = T) (hF : s₀.inFunction = false)
    (hL : s₀.loopDepth = 0) {ds ds' : Array Decl} {b : Bool} {st st' : ParseState}
    (hI : Ready st ∧ Kept s₀ st ∧ ∀ d ∈ ds.toList, d.wf T = true ∧ DeclOK T d)
    (h : Parse.declStep ds st = .ok (ds', b) st') :
    Ready st' ∧ Kept s₀ st' ∧ ∀ d ∈ ds'.toList, d.wf T = true ∧ DeclOK T d := by
  obtain ⟨hR, hK, hall⟩ := hI
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.declStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases he : x.isEof = true
  · rw [if_pos he] at h; simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨hR, hK, hall⟩
  rw [if_neg he, Parse.pure_bind, Parse.bind_ok] at h
  obtain ⟨d, s₁, hd, h⟩ := h
  obtain ⟨hR₁, hK₁, hw, hok⟩ := parseDecl_wf _ _ _ hR (hK.target_eq.trans hT) (hK.inFunction_eq.trans hF)
    (hK.loopDepth_eq.trans hL) hd
  simp only [Parse.pure_ok, Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, rfl⟩ := h
  refine ⟨hR₁, hK.trans hK₁, fun d' hd' => ?_⟩
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hd'
  rcases hd' with hd' | rfl
  · exact hall d' hd'
  · exact ⟨hw, hok⟩

/-- `parseModule` gives a well-formed module, and every line it prints has
words that lex back. -/
theorem parseModule_wf {T : Edition} {s s' : ParseState} {m : Module} (hR : Ready s) (hT : s.target = T)
    (hF : s.inFunction = false) (hL : s.loopDepth = 0) (h : Parse.parseModule s = .ok m s') :
    m.wf T = true ∧ ∀ l ∈ m.lines, WordsOK T l.2 := by
  simp only [Parse.parseModule] at h
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
  obtain ⟨ds, s₁, hds, h⟩ := h
  obtain ⟨_, _, hall⟩ := (iterate_inv
    (I := fun a st => Ready st ∧ Kept s st ∧ ∀ d ∈ a.toList, d.wf T = true ∧ DeclOK T d)
    (fun _ _ _ _ _ hI hst => declStep_wf hT hF hL hI hst) _ #[] s ds s₁ ⟨hR, Kept.refl _, by simp⟩ hds).1
  simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, fun l hl => ?_⟩
  · simp only [Module.wf, List.all_eq_true]
    exact fun d hd => (hall d (by simpa using hd)).1
  · simp only [Module.lines, List.mem_flatMap] at hl
    obtain ⟨d, hd, hl⟩ := hl
    exact (hall d (by simpa using hd)).2 l hl

/-- Every module that `parseTokens` gives from tokens that the lexer could give
is well formed, and every line it prints has words that lex back. The tokens
that the lexer could give end with the end of the file, and every other kind
is one that the lexer gives. -/
theorem parseTokens_wf {toks : List Token} {T : Edition} {m : Module}
    (hlast : ∃ r e, toks = r ++ [e] ∧ e.kind = .eof)
    (hlex : ∀ t ∈ toks, t.kind = .eof ∨ TokenKind.ok T t.kind = true)
    (h : parseTokens toks T = .ok m) : m.wf T = true ∧ ∀ l ∈ m.lines, WordsOK T l.2 := by
  obtain ⟨r, e, rfl, he⟩ := hlast
  simp only [parseTokens] at h
  split at h
  · rename_i m' s' hm
    simp only [Except.ok.injEq] at h; subst h
    exact parseModule_wf ⟨⟨by simp, rfl⟩, by simp, by simpa using he, hlex⟩ rfl rfl rfl hm
  · cases h

end tolean.TypeScript.Syntax
