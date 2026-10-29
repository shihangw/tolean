import tolean.TypeScript.Syntax.RoundTripDecl

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
-/

namespace tolean.TypeScript.Syntax

open tolean

set_option linter.unusedSimpArgs false

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

/-- A kind that the lexer gives: a punctuator is one of `Lex.punctuators`, so
no token stands for `>=` or `>>`, which the lexer gives as `>` tokens. -/
def lexedKind : TokenKind → Bool
  | .punct p => Lex.punctuators.contains p
  | _ => true

/-- The state holds its tokens and their count, the last token is `eof`, the
end of the file, and every token has a kind that the lexer gives. -/
def Ready (s : ParseState) : Prop :=
  Parse.Good s ∧ s.rest.getLast? = some s.eof ∧ s.eof.kind = .eof ∧ ∀ t ∈ s.rest, lexedKind t.kind = true

/-- What reading a node leaves as it was. -/
structure Kept (s s' : ParseState) : Prop where
  eof_eq : s'.eof = s.eof
  inFunction_eq : s'.inFunction = s.inFunction
  loopDepth_eq : s'.loopDepth = s.loopDepth
  target_eq : s'.target = s.target

theorem Kept.refl (s : ParseState) : Kept s s := ⟨rfl, rfl, rfl, rfl⟩

theorem Kept.trans {s₁ s₂ s₃ : ParseState} (h₁ : Kept s₁ s₂) (h₂ : Kept s₂ s₃) : Kept s₁ s₃ :=
  ⟨h₂.eof_eq.trans h₁.eof_eq, h₂.inFunction_eq.trans h₁.inFunction_eq,
    h₂.loopDepth_eq.trans h₁.loopDepth_eq, h₂.target_eq.trans h₁.target_eq⟩

/-- A token that is not the end of the file has a token after it. -/
theorem Ready.more {s : ParseState} {x : Token} {r : List Token} (h : Ready s) (hs : s.rest = x :: r)
    (hx : x.kind ≠ .eof) : r ≠ [] := by
  rintro rfl
  have := h.2.1
  simp [hs] at this
  exact hx (this ▸ h.2.2.1)

/-- A state whose tokens end the tokens of a ready state is ready. -/
theorem Ready.suffix {s s' : ParseState} {a : List Token} (h : Ready s) (hs : s.rest = a ++ s'.rest)
    (hr : s'.rest ≠ []) (hl : s'.left = s'.rest.length) (he : s'.eof = s.eof) : Ready s' := by
  refine ⟨⟨hr, hl⟩, ?_, he ▸ h.2.2.1, fun t ht => h.2.2.2 t (by rw [hs]; exact List.mem_append_right _ ht)⟩
  have h1 := h.2.1
  obtain ⟨u, r', hu⟩ := List.exists_cons_of_ne_nil hr
  rw [hs, hu] at h1
  rw [hu, he]
  simpa [List.getLast?_append] using h1

/-- The state after `advance` reads `x`. -/
abbrev past (s : ParseState) (x : Token) (r : List Token) : ParseState :=
  { s with rest := r, left := s.left - 1, lastStop := x.span.stop }

theorem Ready.past {s : ParseState} {x : Token} {r : List Token} (h : Ready s) (hs : s.rest = x :: r)
    (hr : r ≠ []) : Ready (past s x r) :=
  h.suffix (a := [x]) (by simpa using hs) hr (by have := h.1.2; simp [hs] at this; simp [this]) rfl

theorem Kept.past (s : ParseState) (x : Token) (r : List Token) : Kept s (past s x r) := ⟨rfl, rfl, rfl, rfl⟩

/-- `advance` reads a token that is not the end of the file. -/
theorem advance_past {s : ParseState} {x : Token} {r : List Token} (h : Ready s) (hs : s.rest = x :: r)
    (hx : x.kind ≠ .eof) : Parse.advance s = .ok x (past s x r) :=
  Parse.advance_cons hs (h.more hs hx)

/-- Two runs from one state give one result. -/
theorem ok_unique {α : Type} {x : ParseM α} {s s₁ s₂ : ParseState} {a b : α} (h₁ : x s = .ok a s₁)
    (h₂ : x s = .ok b s₂) : a = b ∧ s₁ = s₂ := by
  rw [h₁] at h₂; cases h₂; exact ⟨rfl, rfl⟩

/-- The tokens that reading from `s` to `s'` takes. -/
def taken (s s' : ParseState) : List Token := s.rest.take (s.rest.length - s'.rest.length)

theorem taken_eq {s s' : ParseState} {a : List Token} (h : s.rest = a ++ s'.rest) : taken s s' = a := by
  simp [taken, h]

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
    · simp [hn, pure, EStateM.pure] at he
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

theorem budget_inv {s s' : ParseState} {n : Nat} (h : Parse.budget s = .ok n s') : s' = s := by
  rw [Parse.budget_eq] at h; cases h; rfl

theorem spanFrom_inv {s s' : ParseState} {p : Pos} {sp : Span} (h : Parse.spanFrom p s = .ok sp s') : s' = s := by
  rw [Parse.spanFrom_eq] at h; cases h; rfl

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
  | .array .., h | .union .., h => by simp [TypeExpr.primaryWF] at h

theorem arrayWF_wf : ∀ t : TypeExpr, t.arrayWF = true → t.wf = true
  | .array _ _, h | .keyword .., h | .null _, h | .literal .., h | .ref .., h | .paren .., h => by
    revert h; simp [TypeExpr.arrayWF, TypeExpr.wf]
  | .union .., h => by simp [TypeExpr.arrayWF] at h

/-- What `p` gives when it reads a type: a type that `ok` accepts, and a state
that is still ready. -/
def GivesT (ok : TypeExpr → Bool) (p : ParseM TypeExpr) : Prop :=
  ∀ s t s', Ready s → p s = .ok t s' → ok t = true ∧ Ready s' ∧ Kept s s'

/-- `skip 2` reads two tokens that another token follows. -/
theorem skip_two {s : ParseState} {x y : Token} {r : List Token} (hs : s.rest = x :: y :: r) (hr : r ≠ []) :
    Parse.skip 2 s = .ok () (past (past s x (y :: r)) y r) := by
  rw [Parse.skip, Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs (by simp))), Parse.skip,
    Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := past s x (y :: r)) rfl hr))]
  rfl

theorem arrayStep_inv {start : Pos} {a a' : TypeExpr} {b : Bool} {s s' : ParseState} (hR : Ready s)
    (h : Parse.arrayStep start a s = .ok (a', b) s') : a'.arrayWF = a.arrayWF ∧ Ready s' ∧ Kept s s' := by
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.arrayStep] at h
  rw [Parse.bind_eq (Parse.peek_eq hs)] at h
  by_cases hc : (!x.isPunct "[" || x.newlineBefore) = true
  · rw [if_pos hc] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨rfl, hR, Kept.refl s⟩
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
      exact ⟨by simp [TypeExpr.arrayWF], hR₂, ⟨rfl, rfl, rfl, rfl⟩⟩
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
theorem unionStep_inv {ok : TypeExpr → Bool} {p : ParseM TypeExpr} (hp : GivesT ok p) {a a' : Array TypeExpr}
    {b : Bool} {s s' : ParseState} (hR : Ready s) (ha : ∀ m ∈ a.toList, ok m = true)
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
    obtain ⟨hmo, hR₁, hK₁⟩ := hp _ _ _ (hR.past hs (hR.more hs hne)) hm
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨push_ok ha hmo, by simp, hR₁, (Kept.past s x r).trans hK₁⟩
  · rw [if_pos (by simp [hx])] at h
    simp only [Parse.pure_ok, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    exact ⟨ha, Nat.le_refl _, hR, Kept.refl s⟩

/-- The steps of the loop over type arguments keep every argument `ok`. -/
theorem typeArgStep_inv {ok : TypeExpr → Bool} {p : ParseM TypeExpr} (hp : GivesT ok p) {a a' : Array TypeExpr}
    {b : Bool} {s s' : ParseState} (hR : Ready s) (ha : ∀ m ∈ a.toList, ok m = true)
    (h : Parse.typeArgStep p a s = .ok (a', b) s') : (∀ m ∈ a'.toList, ok m = true) ∧ Ready s' ∧ Kept s s' := by
  simp only [Parse.typeArgStep] at h
  rw [Parse.bind_ok] at h
  obtain ⟨m, s₁, hm, h⟩ := h
  obtain ⟨hmo, hR₁, hK₁⟩ := hp _ _ _ hR hm
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

@[simp] theorem failAt_bind_ne_ok {α β : Type} (t : Token) (m : String) (f : α → ParseM β) (s s' : ParseState)
    (b : β) : (Parse.failAt (A := α) t m >>= f) s ≠ .ok b s' := by
  simp [Parse.failAt, throw, throwThe, MonadExceptOf.throw, EStateM.throw, bind, EStateM.bind]

@[simp] theorem unexpected_bind_ne_ok {α β : Type} (t : Token) (m : String) (f : α → ParseM β) (s s' : ParseState)
    (b : β) : (Parse.unexpected (A := α) t m >>= f) s ≠ .ok b s' := by
  simp [Parse.unexpected, Parse.failAt, throw, throwThe, MonadExceptOf.throw, EStateM.throw, bind, EStateM.bind]

theorem types_give : ∀ f : Nat, GivesT TypeExpr.wf (Parse.parseType f) ∧
    GivesT TypeExpr.arrayWF (Parse.parseArrayType f) ∧ GivesT TypeExpr.primaryWF (Parse.parsePrimaryType f)
  | 0 => ⟨fun _ _ _ _ h => absurd h (by simp only [Parse.parseType]; exact outOfFuel_ne_ok _ _ _),
      fun _ _ _ _ h => absurd h (by simp only [Parse.parseArrayType]; exact outOfFuel_ne_ok _ _ _),
      fun _ _ _ _ h => absurd h (by simp only [Parse.parsePrimaryType]; exact outOfFuel_ne_ok _ _ _)⟩
  | f + 1 => by
    obtain ⟨ihT, ihA, ihP⟩ := types_give f
    refine ⟨?_, ?_, ?_⟩
    · intro s t s' hR h
      obtain ⟨x, r, hs⟩ := hR.cons
      simp only [Parse.parseType] at h
      rw [Parse.bind_eq (Parse.peek_eq hs)] at h
      -- The members after the first, and the token after them.
      have hloop : ∀ (first : TypeExpr) (s₁ : ParseState) (n : Nat) (members : Array TypeExpr) (s₂ : ParseState),
          first.arrayWF = true → Ready s₁ →
          Parse.iterate n #[first] (Parse.unionStep (Parse.parseArrayType f)) s₁ = .ok members s₂ →
          (∀ m ∈ members.toList, m.arrayWF = true) ∧ 1 ≤ members.size ∧ Ready s₂ ∧ Kept s₁ s₂ :=
        fun first s₁ n members s₂ hfw hR₁ hm => (iterate_inv
          (I := fun a st => (∀ m ∈ a.toList, m.arrayWF = true) ∧ 1 ≤ a.size ∧ Ready st ∧ Kept s₁ st)
          (fun a st a' b st' hI hst => by
            obtain ⟨h1, h2, h3, h4⟩ := unionStep_inv ihA hI.2.2.1 hI.1 hst
            exact ⟨h1, by omega, h3, hI.2.2.2.trans h4⟩) _ _ _ _ _
          ⟨by simpa using hfw, by simp, hR₁, Kept.refl _⟩ hm).1
      have hunion : ∀ (sp : Span) (ms : List TypeExpr), 1 ≤ ms.length → (∀ m ∈ ms, m.arrayWF = true) →
          (TypeExpr.union sp ms).wf = true := by
        intro sp ms hlen hall
        match ms, hlen with
        | [m], _ => simpa [TypeExpr.wf] using hall
        | m₁ :: m₂ :: ms', _ =>
          simp only [TypeExpr.wf, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by simp, (allArrayWF_iff _).mpr hall⟩
      by_cases hl : x.isPunct "|" = true
      · have hne : x.kind ≠ .eof := by simp [Token.isPunct] at hl; rw [hl]; simp
        rw [if_pos hl, Parse.bind_eq (Parse.discard_eq (advance_past hR hs hne)), Parse.bind_ok] at h
        obtain ⟨first, s₁, hf, h⟩ := h
        obtain ⟨hfw, hR₁, hK₁⟩ := ihA _ _ _ (hR.past hs (hR.more hs hne)) hf
        rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
        obtain ⟨members, s₂, hm, h⟩ := h
        obtain ⟨hmall, hsize, hR₂, hK₂⟩ := hloop first s₁ _ members s₂ hfw hR₁ hm
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
        obtain ⟨hfw, hR₁, hK₁⟩ := ihA _ _ _ hR hf
        rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
        obtain ⟨members, s₂, hm, h⟩ := h
        obtain ⟨hmall, hsize, hR₂, hK₂⟩ := hloop first s₁ _ members s₂ hfw hR₁ hm
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
          exact ⟨arrayWF_wf _ hfw, hR₂, hK₁.trans hK₂⟩
    · intro s t s' hR h
      obtain ⟨x, r, hs⟩ := hR.cons
      simp only [Parse.parseArrayType] at h
      rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.budget_eq _), Parse.bind_ok] at h
      obtain ⟨p, s₁, hp, h⟩ := h
      obtain ⟨hpw, hR₁, hK₁⟩ := ihP _ _ _ hR hp
      exact (iterate_inv (I := fun a st => a.arrayWF = true ∧ Ready st ∧ Kept s st)
        (fun a st a' b st' hI hst => by
          obtain ⟨h1, h2, h3⟩ := arrayStep_inv hI.2.1 hst
          exact ⟨h1 ▸ hI.1, h2, hI.2.2.trans h3⟩) _ p s₁ t s' ⟨primaryWF_arrayWF p hpw, hR₁, hK₁⟩ h).1
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
        simp only at h
        obtain ⟨n, r', hr⟩ := hR₁.cons
        rw [Parse.bind_eq (Parse.peek_eq hr)] at h
        by_cases hdot : n.isPunct "." = true
        · simp [hdot] at h
        simp only [hdot, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind] at h
        by_cases hkw : Parse.keywordTypes.contains name = true
        · simp only [hkw, ↓reduceIte, Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simp only [TypeExpr.primaryWF, hkw, Bool.or_true], hR₁, Kept.past _ _ _⟩
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
          exact ⟨by simp [TypeExpr.primaryWF, TypeExpr.allWF, hname], hR₁, Kept.past _ _ _⟩
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind] at h
        have hn : n.kind = .punct "<" := by simp [Token.isPunct] at hlt; exact hlt.1
        have hne : n.kind ≠ .eof := by rw [hn]; simp
        rw [Parse.bind_eq (Parse.discard_eq (advance_past hR₁ hr hne)), Parse.bind_eq (Parse.budget_eq _),
          Parse.bind_ok] at h
        obtain ⟨args, s₂, hargs, h⟩ := h
        have hR₂ := hR₁.past hr (hR₁.more hr hne)
        obtain ⟨hall, hR₃, hK₃⟩ := (iterate_inv
          (I := fun a st => (∀ m ∈ a.toList, m.wf = true) ∧ Ready st ∧ Kept (past (past s t0 r) n r') st)
          (fun a st a' b st' hI hst => by
            obtain ⟨h1, h2, h3⟩ := typeArgStep_inv ihT hI.2.1 hI.1 hst
            exact ⟨h1, h2, hI.2.2.trans h3⟩) _ #[] _ args s₂ ⟨by simp, hR₂, Kept.refl _⟩ hargs).1
        rw [Parse.bind_ok] at h
        obtain ⟨c, s₄, hc, h⟩ := h
        obtain ⟨_, r₄, _, rfl, hR₄⟩ := expectPunct_inv hR₃ hc
        rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
        simp only [Parse.pure_ok] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp [TypeExpr.primaryWF, hname, (allWF_iff _).mpr hall], hR₄,
          (Kept.past _ _ _).trans ((Kept.past _ _ _).trans (hK₃.trans (Kept.past _ _ _)))⟩
      | keyword w =>
        obtain ⟨rfl, hR₁⟩ := hpast (by simp)
        by_cases h1 : w = "void"
        · subst h1; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simp [TypeExpr.primaryWF], hR₁, Kept.past _ _ _⟩
        by_cases h2 : w = "null"
        · subst h2; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simp [TypeExpr.primaryWF], hR₁, Kept.past _ _ _⟩
        by_cases h3 : w = "true"
        · subst h3; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simp [TypeExpr.primaryWF], hR₁, Kept.past _ _ _⟩
        by_cases h4 : w = "false"
        · subst h4; simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simp [TypeExpr.primaryWF], hR₁, Kept.past _ _ _⟩
        simp [h1, h2, h3, h4] at h
      | string v | number v | bigint v =>
        obtain ⟨rfl, hR₁⟩ := hpast (by simp)
        simp only [Parse.pure_ok] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp [TypeExpr.primaryWF], hR₁, Kept.past _ _ _⟩
      | punct p =>
        obtain ⟨rfl, hR₁⟩ := hpast (by simp)
        by_cases hp : p = "("
        · subst hp
          simp only at h
          rw [Parse.bind_ok] at h
          obtain ⟨inner, s₂, hi, h⟩ := h
          obtain ⟨hiw, hR₂, hK₂⟩ := ihT _ _ _ hR₁ hi
          rw [Parse.bind_ok] at h
          obtain ⟨c, s₃, hc, h⟩ := h
          obtain ⟨_, r₃, _, rfl, hR₃⟩ := expectPunct_inv hR₂ hc
          rw [Parse.bind_eq (Parse.spanFrom_eq _ _)] at h
          simp only [Parse.pure_ok] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simpa [TypeExpr.primaryWF] using hiw, hR₃,
            (Kept.past _ _ _).trans (hK₂.trans (Kept.past _ _ _))⟩
        · simp [hp] at h
      | eof => simp at h

/-! ### Operators -/

theorem skip_inv {s s' : ParseState} {a r : List Token} (h : Ready s) (hs : s.rest = a ++ r) (hr : r ≠ [])
    (hk : Parse.skip a.length s = .ok () s') : s'.rest = r ∧ Ready s' ∧ Kept s s' := by
  obtain ⟨s'', h1, hL⟩ := Parse.skip_ok a hs hr h.1.2
  obtain ⟨_, rfl⟩ := ok_unique hk h1
  have hK : Kept s s' := ⟨hL.eof_eq, hL.inFunction_eq, hL.loopDepth_eq, hL.target_eq⟩
  exact ⟨hL.rest_eq, h.suffix (by rw [hs, hL.rest_eq]) (by rw [hL.rest_eq]; exact hr)
    (by rw [hL.left_eq, hL.rest_eq]) hL.eof_eq, hK⟩

theorem Parse.peekAt_eq' (k : Nat) (s : ParseState) : Parse.peekAt k s = .ok (s.rest[k]?.getD s.eof) s := by
  simp [Parse.peekAt, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]

theorem peekAt_inv {s s' : ParseState} {k : Nat} {t : Token} (h : Parse.peekAt k s = .ok t s') :
    s' = s ∧ t = s.rest[k]?.getD s.eof := by
  simp [Parse.peekAt, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure] at h
  exact ⟨h.2.symm, h.1.symm⟩

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
  cases op <;> simp_all (config := { decide := true }) [symbol, BinOp.symbol, Lex.punctuators, Lex.reservedWords, punctWord]

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
  rw [Parse.bind_eq (Parse.peekAt_eq' 0 s), Parse.bind_eq (Parse.peekAt_eq' 1 s),
    Parse.bind_eq (Parse.peekAt_eq' 2 s), Parse.bind_eq (Parse.peekAt_eq' 3 s)]
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
  have hlex : lexedKind x.kind = true := h.2.2.2 x (by simp [hs])
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
        by simp (config := { decide := true }) [hk, symbol, BinOp.symbol, Lex.reservedWords, keywordWord],
        h.more hs (by rw [hk]; simp)⟩
    by_cases h2 : kw = "instanceof"
    · subst h2
      simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨rfl, fun op w he => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨[x], r, by simpa using hs, rfl,
        by simp (config := { decide := true }) [hk, symbol, BinOp.symbol, Lex.reservedWords, keywordWord],
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
    · simp only [hg] at hp
      simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨rfl, fun op w he => ?_⟩
      obtain ⟨op', hop', heq⟩ := Option.map_eq_some_iff.mp he
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      have hsym := ofSymbol_binOp hop'
      have hl : Lex.punctuators.contains op'.symbol = true := by rw [hsym]; simpa [lexedKind] using hlex
      exact ⟨[x], r, by simpa using hs, rfl, by rw [symbol_binOp_punct hl (by rw [hsym]; exact hg), hsym]; simp [hk],
        h.more hs (by rw [hk]; simp)⟩
  | _ =>
    simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
    exact ⟨rfl, fun _ _ he => by simp at he⟩

theorem symbol_assignOp_punct {op : AssignOp} (hl : Lex.punctuators.contains op.symbol = true)
    (hgt : op.symbol ≠ ">") : symbol op.symbol = [.punct op.symbol] := by
  cases op <;> simp_all (config := { decide := true }) [symbol, AssignOp.symbol, Lex.punctuators,
    Lex.reservedWords, punctWord]

/-- `peekAssignOp` changes nothing, and it gives an operator whose tokens come first. -/
theorem peekAssignOp_inv {s s' : ParseState} {v : Option (AssignOp × Nat)} (h : Ready s)
    (hp : Parse.peekAssignOp s = .ok v s') : s' = s ∧ ∀ op w, v = some (op, w) →
      ∃ a r, s.rest = a ++ r ∧ a.length = w ∧ a.map (·.kind) = symbol op.symbol ∧ r ≠ [] := by
  obtain ⟨x, r, hs⟩ := h.cons
  have hlex : lexedKind x.kind = true := h.2.2.2 x (by simp [hs])
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
    · simp only [hg] at hp
      simp only [Parse.pure_ok] at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨rfl, fun op w he => ?_⟩
      obtain ⟨op', hop', heq⟩ := Option.map_eq_some_iff.mp he
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      have hsym := ofSymbol_assignOp hop'
      have hl : Lex.punctuators.contains op'.symbol = true := by rw [hsym]; simpa [lexedKind] using hlex
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
    by_cases h1 : p = "!"; · subst h1; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord]
    by_cases h2 : p = "-"; · subst h2; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord]
    by_cases h3 : p = "+"; · subst h3; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord]
    by_cases h4 : p = "~"; · subst h4; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord]
    simp [h1, h2, h3, h4] at h
  | keyword w =>
    by_cases h1 : w = "typeof"; · subst h1; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, Lex.reservedWords, keywordWord]
    by_cases h2 : w = "void"; · subst h2; simp at h; subst h; simp (config := { decide := true }) [symbol, UnaryOp.symbol, Lex.reservedWords, keywordWord]
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
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Parse.pure_ok] at h
    exact ⟨h.2.symm, hc⟩
  · simp only [hc, Bool.not_false, ↓reduceIte] at h; exact absurd h (Parse.failAt_ne_ok _ _ _ _ _)

theorem peek_eq' (s : ParseState) : Parse.peek s = .ok (s.rest[0]?.getD s.eof) s := Parse.peekAt_eq' 0 s

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
  rw [Parse.bind_eq (peek_eq' s), Parse.bind_eq (Parse.peekAt_eq' 1 s)] at h
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
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    exact ⟨⟨⟨⟨⟨by omega, h2⟩, wfAt_bin_mono hm h3⟩, h4⟩, h5⟩, h6⟩
  | .ident .., h | .number .., h | .bigint .., h | .string .., h | .bool .., h | .null _, h | .array .., h
  | .object .., h | .paren .., h | .member .., h | .index .., h | .call .., h | .unary .., h | .prefix .., h
  | .postfix .., h | .cond .., h | .assign .., h => by simp_all [Expr.wfAt]

theorem wfAt_cond_of_bin {T : Edition} {m : Nat} : ∀ {e : Expr}, e.wfAt T (.bin m) = true → e.wfAt T .cond = true := by
  intro e h
  have h0 := wfAt_bin_mono (Nat.zero_le m) h
  cases e <;> simp_all [Expr.wfAt]

theorem wfAt_assign_of_cond {T : Edition} : ∀ {e : Expr}, e.wfAt T .cond = true → e.wfAt T .assign = true := by
  intro e h; cases e <;> simp_all [Expr.wfAt]

/-! ### What the expression parser gives -/

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

def GivesE (T : Edition) (level : Level) (p : ParseM Expr) : Prop :=
  ∀ s e s', Ready s → s.target = T → p s = .ok e s' → GaveE T level s e s'

theorem GaveE.lift {T : Edition} {l l' : Level} {s s' : ParseState} {e : Expr} (h : GaveE T l s e s')
    (hw : e.wfAt T l = true → e.wfAt T l' = true) : GaveE T l' s e s' :=
  ⟨h.ready, h.kept, h.tokens, hw h.wf, h.after⟩

/-- The printed tokens of an expression are not empty. -/
theorem Expr.tokens_ne (e : Expr) : e.tokens ≠ [] := by
  obtain ⟨k, hk, _⟩ := Expr.first e
  intro h; rw [h] at hk; simp at hk

/-- The first token of `a ++ b`, when `a` has the first token of `e`. -/
theorem head_src {src rest : List Token} {e : Expr} (h : (src.map (·.kind)).head? = e.tokens.head?) :
    ((src ++ rest).map (·.kind)).head? = e.tokens.head? := by
  obtain ⟨k, hk, _⟩ := Expr.first e
  rw [hk] at h ⊢
  cases src with
  | nil => simp at h
  | cons x xs => simpa using h

/-- The first token of `src ++ x`, when `src` has the first token of `ks`. -/
theorem head_append2 {src x : List Token} {ks y : List TokenKind} (hks : ks ≠ [])
    (h : (src.map (·.kind)).head? = ks.head?) : ((src ++ x).map (·.kind)).head? = (ks ++ y).head? := by
  cases ks with
  | nil => exact absurd rfl hks
  | cons k ks => cases src with
    | nil => simp at h
    | cons t src => simpa using h

section
variable {sp : Span}

theorem tokens_assign {op : AssignOp} {t v : Expr} :
    (Expr.assign sp op t v).tokens = t.tokens ++ (symbol op.symbol ++ v.tokens) := by
  simp [Expr.tokens, Expr.words]

theorem tokens_binary {op : BinOp} {l r : Expr} :
    (Expr.binary sp op l r).tokens = l.tokens ++ (symbol op.symbol ++ r.tokens) := by
  simp [Expr.tokens, Expr.words]

theorem tokens_cond {t a b : Expr} :
    (Expr.cond sp t a b).tokens = t.tokens ++ (.punct "?" :: a.tokens ++ (.punct ":" :: b.tokens)) := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem tokens_unary {op : UnaryOp} {a : Expr} : (Expr.unary sp op a).tokens = symbol op.symbol ++ a.tokens := by
  simp [Expr.tokens, Expr.words]

theorem tokens_prefix {op : UpdateOp} {a : Expr} :
    (Expr.prefix sp op a).tokens = .punct op.symbol :: a.tokens := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem tokens_postfix {op : UpdateOp} {a : Expr} :
    (Expr.postfix sp op a).tokens = a.tokens ++ [.punct op.symbol] := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem tokens_member {o : Expr} {n : String} :
    (Expr.member sp o n).tokens = o.tokens ++ (.punct "." :: propertyName n) := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem tokens_index {o i : Expr} :
    (Expr.index sp o i).tokens = o.tokens ++ (.punct "[" :: i.tokens ++ [.punct "]"]) := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem tokens_call {c : Expr} {args : List Expr} :
    (Expr.call sp c args).tokens = c.tokens ++ (enclose "(" ")" (Expr.wordsOf args)).flatten := by
  simp [Expr.tokens, Expr.words]

theorem tokens_paren {i : Expr} : (Expr.paren sp i).tokens = .punct "(" :: i.tokens ++ [.punct ")"] := by
  simp [Expr.tokens, Expr.words, punctWord]

end

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
  cases op <;> simp (config := { decide := true }) [symbol, AssignOp.symbol, Lex.reservedWords, punctWord]

theorem symbol_binOp_head (op : BinOp) : (symbol op.symbol).head? ≠ some (.punct "{") := by
  cases op <;> simp (config := { decide := true }) [symbol, BinOp.symbol, Lex.reservedWords, punctWord,
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
  refine ⟨gv.ready, gl.kept.trans (hK₂.trans gv.kept), ⟨lsrc ++ a ++ vsrc, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hl1, hst]; simp
  · rw [tokens_assign]; simp only [List.map_append, skel_append, hl2, hk, hv2, List.append_assoc]
  · rw [tokens_assign, List.append_assoc]; exact head_append2 (Expr.tokens_ne lhs) hl3
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
    (hC : GivesE T .cond (Parse.parseConditional f)) : GivesE T .assign (Parse.parseAssign (f + 1)) := by
  intro s e s' hR hT h
  obtain ⟨x, r, hs⟩ := hR.cons
  simp only [Parse.parseAssign] at h
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

end tolean.TypeScript.Syntax
