import tolean.TypeScript.Syntax.RegExp

namespace tolean.TypeScript.Syntax.RegExp

def isLineBreak (c : Char) : Bool :=
  c == '\n' || c == '\r' || c.toNat == 0x2028 || c.toNat == 0x2029

/-- Read after an opening slash. Keep escapes intact for the Pattern parser.
An escaped slash, or a slash inside a character class, does not end it. -/
def readBody (escaped inClass : Bool) (acc : List Char) :
    List Char → Except String (List Char × List Char)
  | [] => .error "unterminated regular expression literal"
  | c :: cs =>
    if isLineBreak c then .error "line break in regular expression literal"
    else if escaped then readBody false inClass (c :: acc) cs
    else if c == '\\' then readBody true inClass (c :: acc) cs
    else if c == '[' then readBody false true (c :: acc) cs
    else if c == ']' then readBody false false (c :: acc) cs
    else if c == '/' && !inClass then .ok (acc.reverse, cs)
    else readBody false inClass (c :: acc) cs

/-- A successful scan reads the same body regardless of the text after the
closing slash. -/
theorem readBody_frame (chars : List Char) (escaped inClass : Bool)
    (acc body rest : List Char)
    (h : readBody escaped inClass acc chars = .ok (body, rest)) :
    ∃ consumed, chars = consumed ++ '/' :: rest ∧ body = acc.reverse ++ consumed ∧
      ∀ tail, readBody escaped inClass acc (consumed ++ '/' :: tail) = .ok (body, tail) := by
  induction chars generalizing escaped inClass acc with
  | nil => simp [readBody] at h
  | cons c cs ih =>
    simp only [readBody] at h
    split at h
    · contradiction
    · split at h
      · obtain ⟨consumed, hchars, hbody, htail⟩ := ih false inClass (c :: acc) h
        refine ⟨c :: consumed, ?_, ?_, ?_⟩
        · simp [hchars]
        · simpa [List.reverse_cons, List.append_assoc] using hbody
        · intro tail
          simp_all [readBody]
      · split at h
        · obtain ⟨consumed, hchars, hbody, htail⟩ := ih true inClass (c :: acc) h
          refine ⟨c :: consumed, ?_, ?_, ?_⟩
          · simp [hchars]
          · simpa [List.reverse_cons, List.append_assoc] using hbody
          · intro tail
            simp_all [readBody]
        · split at h
          · obtain ⟨consumed, hchars, hbody, htail⟩ := ih false true (c :: acc) h
            refine ⟨c :: consumed, ?_, ?_, ?_⟩
            · simp [hchars]
            · simpa [List.reverse_cons, List.append_assoc] using hbody
            · intro tail
              simp_all [readBody]
          · split at h
            · obtain ⟨consumed, hchars, hbody, htail⟩ := ih false false (c :: acc) h
              refine ⟨c :: consumed, ?_, ?_, ?_⟩
              · simp [hchars]
              · simpa [List.reverse_cons, List.append_assoc] using hbody
              · intro tail
                simp_all [readBody]
            · split at h
              · refine ⟨[], ?_, ?_, ?_⟩
                · simp_all
                · simp_all
                · intro tail
                  simp_all [readBody]
              · obtain ⟨consumed, hchars, hbody, htail⟩ := ih false inClass (c :: acc) h
                refine ⟨c :: consumed, ?_, ?_, ?_⟩
                · simp [hchars]
                · simpa [List.reverse_cons, List.append_assoc] using hbody
                · intro tail
                  simp_all [readBody]

theorem readBody_length {chars body rest : List Char}
    (h : readBody false false [] chars.tail = .ok (body, rest)) :
    chars.length - rest.length = body.length + 2 := by
  obtain ⟨consumed, hc, hb, _⟩ := readBody_frame chars.tail false false [] body rest h
  simp only [List.reverse_nil, List.nil_append] at hb
  subst body
  cases chars with
  | nil => simp [readBody] at h
  | cons c cs =>
    simp only [List.tail_cons] at hc
    simp [hc]
    omega

theorem readBody_replay (chars body rest : List Char)
    (h : readBody false false [] chars = .ok (body, rest)) (tail : List Char) :
    readBody false false [] (body ++ '/' :: tail) = .ok (body, tail) := by
  obtain ⟨consumed, _, hbody, htail⟩ := readBody_frame chars false false [] body rest h
  simp only [List.reverse_nil, List.nil_append] at hbody
  subst body
  exact htail tail

/-- A printable body cannot open a comment, and its closing slash must be
read as its delimiter. Pattern validation is independent of the suffix. -/
def bodyOK (target : Edition) (source : String) : Bool :=
  source.toList.take 3 == ['(', '?', ':'] &&
    (match readBody false false [] (source.toList ++ ['/']) with
     | .ok (body, []) => body == source.toList
     | _ => false) &&
    (match parse source target with
     | .ok _ => true
     | .error _ => false)

theorem bodyOK_parts {T : Edition} {source : String} (h : bodyOK T source = true) :
    source.toList.take 3 = ['(', '?', ':'] ∧
    readBody false false [] (source.toList ++ ['/']) = .ok (source.toList, []) ∧
    ∃ p n, parse source T = .ok (p, n) := by
  simp only [bodyOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hp, hr⟩, hparse⟩ := h
  refine ⟨hp, ?_, ?_⟩
  · cases he : readBody false false [] (source.toList ++ ['/']) with
    | error e => simp [he] at hr
    | ok result =>
      rcases result with ⟨body, rest⟩
      cases rest with
      | nil =>
        simp only [he, beq_iff_eq] at hr
        subst body
        rfl
      | cons c cs => simp [he] at hr
  · cases he : parse source T with
    | error e => simp [he] at hparse
    | ok result => exact ⟨result.1, result.2, rfl⟩

theorem bodyOK_prefix {T : Edition} {source : String} (h : bodyOK T source = true) :
    ∃ rest, source.toList = '(' :: '?' :: ':' :: rest := by
  have hp := (bodyOK_parts h).1
  cases hc : source.toList with
  | nil => simp [hc] at hp
  | cons a cs =>
    cases cs with
    | nil => simp [hc] at hp
    | cons b cs =>
      cases cs with
      | nil => simp [hc] at hp
      | cons c cs =>
        simp [hc] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        exact ⟨cs, rfl⟩

theorem bodyOK_read {T : Edition} {source : String} (h : bodyOK T source = true)
    (tail : List Char) :
    readBody false false [] (source.toList ++ '/' :: tail) = .ok (source.toList, tail) :=
  readBody_replay _ _ _ (bodyOK_parts h).2.1 tail

end tolean.TypeScript.Syntax.RegExp
