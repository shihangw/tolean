import tolean.TypeScript.Syntax.RoundTripExpr

/-! Predicate annotations occur only in a function's return type. -/
namespace tolean.TypeScript.Syntax
open tolean

theorem parseReturnType_plain {s s' : ParseState} {t : TypeExpr} {next : Token} {rest : List Token}
    (hp : Parse.parseType (10 * (s.left + 1)) s = .ok t s')
    (hs : s'.rest = next :: rest) (hn : next.isIdent "is" = false) :
    Parse.parseReturnType s = .ok t s' := by
  simp [Parse.parseReturnType, Parse.budget_eq, hp, Parse.peek_eq hs, hn,
    bind, EStateM.bind, pure, EStateM.pure]

theorem parseReturnType_predicate {s s₁ s₂ : ParseState} {sp : Span} {name : String}
    {isTok : Token} {rest : List Token} {target : TypeExpr}
    (hp : Parse.parseType (10 * (s.left + 1)) s = .ok (.ref sp name []) s₁)
    (hs : s₁.rest = isTok :: rest) (hr : rest ≠ [])
    (hk : isTok.kind = .ident "is") (hn : isTok.newlineBefore = false)
    (ht : Parse.parseType (10 * ((past s₁ isTok rest).left + 1)) (past s₁ isTok rest) = .ok target s₂) :
    Parse.parseReturnType s = .ok (.predicate ⟨sp.start, s₂.lastStop⟩ name target) s₂ := by
  simp only [Parse.parseReturnType]
  rw [Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hp, Parse.bind_eq (Parse.peek_eq hs)]
  rw [if_pos (by simp [Token.isIdent, hk, hn]), Parse.pure_bind]
  simp only []
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs hr)), Parse.bind_eq (Parse.budget_eq _)]
  rw [Parse.bind_eq ht, Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl

theorem parseReturnType_regular_reads (t : TypeExpr) (ht : t.wf = true)
    (s : ParseState) (ts rest : List Token) (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length)
    (hk : ts.map (·.kind) = t.tokens) (hn : ∀ y ∈ ts, NoBreak y) (hr : rest ≠ [])
    (hf : FollowsType rest) (hi : ∀ y ∈ rest.head?, y.isIdent "is" = false) :
    ∃ t' s', Parse.parseReturnType s = .ok t' s' ∧ t'.erase = t.erase ∧ Leaves s s' rest := by
  obtain ⟨t', s', hp, he, hL⟩ := parseType_budget t ht s ts rest hs hl hk hn hr hf
  obtain ⟨next, tail, rfl⟩ := List.exists_cons_of_ne_nil hr
  exact ⟨t', s', parseReturnType_plain hp hL.rest_eq (hi next (by simp)), he, hL⟩

theorem parseReturnType_predicate_reads (sp : Span) (name : String) (target : TypeExpr)
    (hnm : typeName name = true) (ht : target.wf = true)
    (s : ParseState) (ts rest : List Token) (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length)
    (hk : ts.map (·.kind) = (TypeExpr.predicate sp name target).tokens)
    (hn : ∀ y ∈ ts, NoBreak y) (hr : rest ≠ []) (hf : FollowsType rest) :
    ∃ t' s', Parse.parseReturnType s = .ok t' s' ∧
      t'.erase = (TypeExpr.predicate sp name target).erase ∧ Leaves s s' rest := by
  simp only [TypeExpr.tokens, TypeExpr.words, identWord, List.flatten_cons,
    List.singleton_append] at hk
  obtain ⟨nm, ts₁, rfl⟩ := List.exists_cons_of_ne_nil (show ts ≠ [] by intro h; subst h; simp at hk)
  obtain ⟨isTok, tts, rfl⟩ := List.exists_cons_of_ne_nil (show ts₁ ≠ [] by intro h; subst h; simp at hk)
  simp only [List.map_cons, List.cons.injEq] at hk
  obtain ⟨hnmTok, hisTok, htt⟩ := hk
  have hs' : s.rest = nm :: isTok :: (tts ++ rest) := by simpa using hs
  have hfIs : FollowsType (isTok :: (tts ++ rest)) := by
    simp [FollowsType, FollowsArray, FollowsPrimary, hisTok]
  obtain ⟨first, s₁', hp, he, hL₁⟩ := parseType_budget (.ref sp name [])
    (by simp [TypeExpr.wf, hnm, TypeExpr.allWF]) s [nm] (isTok :: (tts ++ rest))
    (by simpa using hs') hl (by simp [TypeExpr.tokens, TypeExpr.words, identWord, hnmTok])
    (fun y hy => hn y (by simp at hy; simp [hy])) (by simp) hfIs
  obtain ⟨sp', rfl⟩ : ∃ sp', first = .ref sp' name [] := by
    cases first <;> simp [TypeExpr.erase] at he
    case ref sp' n args =>
      obtain ⟨rfl, ha⟩ := he
      cases args <;> simp [TypeExpr.eraseAll] at ha
      exact ⟨sp', rfl⟩
  let s₂ := past s₁' isTok (tts ++ rest)
  have hl₂ : s₂.left = s₂.rest.length := by
    simp [s₂, hL₁.left_eq]
  obtain ⟨target', s₃, hpt, het, hL₃⟩ := parseType_budget target ht s₂ tts rest
    rfl hl₂ htt (fun y hy => hn y (by simp [hy])) hr hf
  refine ⟨.predicate ⟨sp'.start, s₃.lastStop⟩ name target', s₃, ?_, ?_, ?_⟩
  · exact parseReturnType_predicate hp hL₁.rest_eq (by simp [hr]) hisTok
      (hn isTok (by simp) (by rw [hisTok]; simp)) hpt
  · simp [TypeExpr.erase, het]
  · exact leaves_trans hL₁ (leaves_trans
      (leaves_advance hL₁.rest_eq (by rw [hL₁.left_eq, hL₁.rest_eq])) hL₃)

theorem parseReturnType_reads (t : TypeExpr) (ht : t.returnWF = true)
    (s : ParseState) (ts rest : List Token) (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length)
    (hk : ts.map (·.kind) = t.tokens) (hn : ∀ y ∈ ts, NoBreak y) (hr : rest ≠ [])
    (hf : FollowsType rest) (hi : ∀ y ∈ rest.head?, y.isIdent "is" = false) :
    ∃ t' s', Parse.parseReturnType s = .ok t' s' ∧ t'.erase = t.erase ∧ Leaves s s' rest := by
  cases t with
  | predicate sp name target =>
    simp only [TypeExpr.returnWF, Bool.and_eq_true] at ht
    exact parseReturnType_predicate_reads sp name target ht.1 ht.2 s ts rest hs hl hk hn hr hf
  | _ => exact parseReturnType_regular_reads _ ht s ts rest hs hl hk hn hr hf hi

end tolean.TypeScript.Syntax
