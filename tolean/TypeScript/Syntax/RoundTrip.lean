import tolean.TypeScript.EStateM
import tolean.TypeScript.Syntax.Layout

/-!
The parser's round trip, on tokens: the parser reads the tokens that
`Syntax/Source.lean` prints for a tree as the same tree, apart from spans.

The theorems here are about the tokens that the lexer gives for the printed
source. `Syntax/RoundTripLex.lean` relates the printed characters to these
tokens, and `Syntax/RoundTripText.lean` puts the steps together as the round
trip on source text.

`types_reads` covers well-formed types. A type is well formed when it has
the shape that `parseType` reads: a union has two members or more, or one
after a `|`, and each member is a primary type with `[]` after it any number
of times. `types_give` in `Syntax/ParseWF.lean` proves that every type the
parser gives is well formed.
`Reads p t follows`
states that `p` reads the tokens of `t`, followed by any tokens that
`follows` allows, as `t` apart from spans, and leaves those tokens. Each
loop of the parser is a named step, such as `Parse.unionStep`, so that a
lemma such as `iterate_sepBefore` can state what the loop reads.

`Syntax/RoundTripExpr.lean` covers expressions, `Syntax/RoundTripStmt.lean`
statements, and `Syntax/RoundTripDecl.lean` declarations and modules.
-/
namespace tolean.TypeScript.Syntax

open tolean

/-! ### The parser's monad -/

namespace Parse

variable {α β : Type}

-- `ParseM` is an `EStateM`, so the shared lemmas apply.
export EStateM (bind_ok bind_eq ite_state pure_ok get_ok modify_eq)

@[simp] theorem failAt_ne_ok (t : Token) (m : String) (s s' : ParseState) (a : α) :
    (failAt (A := α) t m) s ≠ .ok a s' := by
  simp [failAt, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

@[simp] theorem unexpected_ne_ok (t : Token) (m : String) (s s' : ParseState) (a : α) :
    (unexpected (A := α) t m) s ≠ .ok a s' := by
  simp [unexpected, failAt, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- The state holds its tokens, and the count of them. -/
def Good (s : ParseState) : Prop := s.rest ≠ [] ∧ s.left = s.rest.length

theorem peek_eq {s : ParseState} {t : Token} {r : List Token} (h : s.rest = t :: r) :
    peek s = .ok t s := by
  simp [peek, peekAt, h, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure,
    EStateM.pure]

theorem peekAt_eq {s : ParseState} {k : Nat} {t : Token} (h : s.rest[k]? = some t) :
    peekAt k s = .ok t s := by
  simp [peekAt, h, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure,
    EStateM.pure]

/-- `advance` reads a token that another token follows. -/
theorem advance_eq {s : ParseState} {t u : Token} {r : List Token} (h : s.rest = t :: u :: r) :
    advance s = .ok t { s with rest := u :: r, left := s.left - 1, lastStop := t.span.stop } := by
  simp [advance, h, get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
    bind, EStateM.bind, pure, EStateM.pure]

theorem iterate_succ {σ : Type} (fuel : Nat) (st : σ) (step : σ → ParseM (σ × Bool)) :
    iterate (fuel + 1) st step = (do
      let (st', again) ← step st
      if again then iterate fuel st' step else return st') := by
  rw [iterate]

end Parse

/-! ### Types -/

/-- A name that `parsePrimaryType` reads as the name of a type. -/
def typeName (n : String) : Bool :=
  !Parse.keywordTypes.contains n && !Parse.typeOperatorWords.contains n &&
    !Parse.refusedNames.contains n

mutual

/-- `t` is a type that `parsePrimaryType` reads: no `|` and no `[]` outside
parentheses. -/
def TypeExpr.primaryWF : TypeExpr → Bool
  | .keyword _ name => name == "void" || Parse.keywordTypes.contains name
  | .null _ => true
  | .literal _ _ => true
  | .ref _ name args => typeName name && TypeExpr.allWF args
  | .paren _ inner => inner.wf
  | .array .. | .union .. => false

/-- `t` is a type that `parseArrayType` reads: a primary type, with `[]`
after it any number of times. -/
def TypeExpr.arrayWF : TypeExpr → Bool
  | .array _ elem => elem.arrayWF
  | .keyword _ name => name == "void" || Parse.keywordTypes.contains name
  | .null _ => true
  | .literal _ _ => true
  | .ref _ name args => typeName name && TypeExpr.allWF args
  | .paren _ inner => inner.wf
  | .union .. => false

/-- `t` is a type that `parseType` reads. A union has two members or more, or
one after a `|`, and each member is a type that `parseArrayType` reads. -/
def TypeExpr.wf : TypeExpr → Bool
  | .union _ [member] => member.arrayWF
  | .union _ members => 2 ≤ members.length && TypeExpr.allArrayWF members
  | .array _ elem => elem.arrayWF
  | .keyword _ name => name == "void" || Parse.keywordTypes.contains name
  | .null _ => true
  | .literal _ _ => true
  | .ref _ name args => typeName name && TypeExpr.allWF args
  | .paren _ inner => inner.wf

def TypeExpr.allWF : List TypeExpr → Bool
  | [] => true
  | t :: ts => t.wf && TypeExpr.allWF ts

def TypeExpr.allArrayWF : List TypeExpr → Bool
  | [] => true
  | t :: ts => t.arrayWF && TypeExpr.allArrayWF ts

end

mutual

/-- How deep `parseType` calls nest to read `t`: one step for each `<…>` and
each `(…)`. -/
def TypeExpr.height : TypeExpr → Nat
  | .ref _ _ args => TypeExpr.heightOf args + 1
  | .paren _ inner => inner.height + 1
  | .array _ elem => elem.height
  | .union _ members => TypeExpr.heightOf members
  | .keyword .. | .null _ | .literal .. => 0

def TypeExpr.heightOf : List TypeExpr → Nat
  | [] => 0
  | t :: ts => max t.height (TypeExpr.heightOf ts)

end

/-- The kinds of the tokens of `t`. -/
def TypeExpr.tokens (t : TypeExpr) : List TokenKind := t.words.flatten

/-- The first token of `rest` cannot continue a primary type: no `<` of type
arguments and no `.` of a qualified name. -/
def FollowsPrimary (rest : List Token) : Prop :=
  ∀ t ∈ rest.head?, t.kind ≠ .punct "<" ∧ t.kind ≠ .punct "."

/-- Nor a `[` of an array type. -/
def FollowsArray (rest : List Token) : Prop :=
  FollowsPrimary rest ∧ ∀ t ∈ rest.head?, t.kind ≠ .punct "["

/-- Nor a `|` of a union, or an `&`. -/
def FollowsType (rest : List Token) : Prop :=
  FollowsArray rest ∧ ∀ t ∈ rest.head?, t.kind ≠ .punct "|" ∧ t.kind ≠ .punct "&"

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

/-- The state after `advance` reads `x`. -/
abbrev past (s : ParseState) (x : Token) (r : List Token) : ParseState :=
  { s with rest := r, left := s.left - 1, lastStop := x.span.stop }

theorem Kept.past (s : ParseState) (x : Token) (r : List Token) : Kept s (past s x r) := ⟨rfl, rfl, rfl, rfl⟩

/-- What reading `rest` from `s` leaves in the state, apart from `lastStop`. -/
structure Leaves (s s' : ParseState) (rest : List Token) : Prop extends Kept s s' where
  rest_eq : s'.rest = rest
  left_eq : s'.left = rest.length

/-- Reading nothing leaves the state as it was. -/
theorem Leaves.refl {s : ParseState} {rest : List Token} (h : s.rest = rest) (hl : s.left = rest.length) :
    Leaves s s rest :=
  { toKept := Kept.refl s, rest_eq := h, left_eq := hl }

/-- Reading one token `x`, which `r` follows, leaves `r`. -/
theorem leaves_advance {s : ParseState} {x : Token} {r : List Token} (h : s.rest = x :: r)
    (hl : s.left = s.rest.length) : Leaves s (past s x r) r where
  rest_eq := rfl
  left_eq := by simp [hl, h]
  eof_eq := rfl
  inFunction_eq := rfl
  loopDepth_eq := rfl
  target_eq := rfl

theorem noBreak_of {y : Token} {p : String} (hy : y.kind = .punct p) (hp : p ≠ "(") (h : NoBreak y) :
    y.newlineBefore = false :=
  h (by rw [hy]; simpa using hp)

/-- `p` reads the tokens of `t`, followed by any rest that `follows` allows,
as `t` apart from spans, and leaves the rest. -/
def Reads (p : ParseM TypeExpr) (t : TypeExpr) (follows : List Token → Prop) : Prop :=
  ∀ (s : ParseState) (ts rest : List Token), s.rest = ts ++ rest → s.left = s.rest.length →
    ts.map (·.kind) = t.tokens → (∀ x ∈ ts, NoBreak x) → rest ≠ [] → follows rest →
    ∃ t' s', p s = .ok t' s' ∧ t'.erase = t.erase ∧ Leaves s s' rest

/-- A parser that reads one token of kind `k` as `expected`, whatever follows
that `follows` allows, reads every type whose tokens are `[k]`. -/
theorem reads_one {p : ParseM TypeExpr} {t : TypeExpr} {k : TokenKind} {expected : Token → TypeExpr}
    {follows : List Token → Prop} (htok : t.tokens = [k]) (herase : ∀ x, (expected x).erase = t.erase)
    (hp : ∀ s x u r, s.rest = x :: u :: r → x.kind = k → follows (u :: r) →
      p s = .ok (expected x) (past s x (u :: r))) :
    Reads p t follows := by
  intro s ts rest hs hl hk _ hr hf
  rw [htok] at hk
  obtain ⟨x, rfl⟩ : ∃ x, ts = [x] := by
    match ts, hk with
    | [x], _ => exact ⟨x, rfl⟩
  obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  have hs' : s.rest = x :: u :: r := by simpa using hs
  have hx : x.kind = k := by simpa using hk
  exact ⟨_, _, hp s x u r hs' hx hf, herase x, leaves_advance hs' hl⟩

/-- `parsePrimaryType` reads the name of a keyword type, such as `string`, which `u` follows. -/
theorem parsePrimaryType_keyword (f : Nat) (s : ParseState) (x u : Token) (r : List Token) (name : String)
    (hs : s.rest = x :: u :: r) (hx : x.kind = .ident name) (hu : FollowsPrimary (u :: r))
    (hk : name ∈ Parse.keywordTypes) :
    Parse.parsePrimaryType (f + 1) s = .ok (.keyword x.span name) (past s x (u :: r)) := by
  have hdot : u.kind ≠ .punct "." := (hu u rfl).2
  simp [Parse.parsePrimaryType, Parse.advance_eq hs, hx, Parse.peek_eq (s := past s x (u :: r)) rfl,
    Token.isPunct, hdot, hk, bind, EStateM.bind, pure, EStateM.pure]

/-- `parsePrimaryType` reads a type name, which `u` follows. -/
theorem parsePrimaryType_name (f : Nat) (s : ParseState) (x u : Token) (r : List Token) (name : String)
    (hs : s.rest = x :: u :: r) (hx : x.kind = .ident name) (hu : FollowsPrimary (u :: r))
    (hn : typeName name = true) :
    Parse.parsePrimaryType (f + 1) s = .ok (.ref x.span name []) (past s x (u :: r)) := by
  have hdot : u.kind ≠ .punct "." := (hu u rfl).2
  have hlt : u.kind ≠ .punct "<" := (hu u rfl).1
  have hn' : name ∉ Parse.keywordTypes ∧ name ∉ Parse.typeOperatorWords ∧ name ∉ Parse.refusedNames := by
    simpa [typeName, and_assoc] using hn
  simp [Parse.parsePrimaryType, Parse.advance_eq hs, hx, Parse.peek_eq (s := past s x (u :: r)) rfl,
    Token.isPunct, hdot, hlt, hn'.1, hn'.2.1, hn'.2.2, bind, EStateM.bind, pure, EStateM.pure]

/-- The type that `parsePrimaryType` gives for a token other than an
identifier and `(`, when it reads one. -/
def simpleType (x : Token) : Option TypeExpr :=
  match x.kind with
  | .keyword "void" => some (.keyword x.span "void")
  | .keyword "null" => some (.null x.span)
  | .keyword "true" => some (.literal x.span (.bool true))
  | .keyword "false" => some (.literal x.span (.bool false))
  | .string value => some (.literal x.span (.string value))
  | .number text => some (.literal x.span (.number text))
  | .bigint text => some (.literal x.span (.bigint text))
  | _ => none

theorem parsePrimaryType_simple (f : Nat) (s : ParseState) (x u : Token) (r : List Token) (t : TypeExpr)
    (hs : s.rest = x :: u :: r) (ht : simpleType x = some t) :
    Parse.parsePrimaryType (f + 1) s = .ok t (past s x (u :: r)) := by
  unfold simpleType at ht
  split at ht <;> simp only [Option.some.injEq, reduceCtorEq] at ht <;> subst ht <;>
    simp_all [Parse.parsePrimaryType, Parse.advance_eq hs, bind, EStateM.bind, pure, EStateM.pure]

theorem Parse.advance_cons {s : ParseState} {x : Token} {r : List Token} (h : s.rest = x :: r)
    (hr : r ≠ []) : Parse.advance s = .ok x { s with rest := r, left := s.left - 1, lastStop := x.span.stop } := by
  obtain ⟨u, r', rfl⟩ := List.exists_cons_of_ne_nil hr
  exact Parse.advance_eq h

theorem Parse.expectPunct_ok {s : ParseState} {x : Token} {r : List Token} {p : String}
    (h : s.rest = x :: r) (hr : r ≠ []) (hx : x.kind = .punct p) :
    Parse.expectPunct p s = .ok x { s with rest := r, left := s.left - 1, lastStop := x.span.stop } := by
  simp only [Parse.expectPunct, bind, EStateM.bind, Parse.peek_eq h]
  simp [Token.isPunct, hx, Parse.advance_cons h hr]

theorem leaves_trans {s₁ s₂ s₃ : ParseState} {r₂ r₃ : List Token} (h₁ : Leaves s₁ s₂ r₂)
    (h₂ : Leaves s₂ s₃ r₃) : Leaves s₁ s₃ r₃ :=
  { toKept := h₁.toKept.trans h₂.toKept, rest_eq := h₂.rest_eq, left_eq := h₂.left_eq }

/-- `( T )`, when `parseType` reads `T`. -/
theorem parsePrimaryType_paren (f : Nat) (sp : Span) (inner : TypeExpr)
    (h : Reads (Parse.parseType f) inner FollowsType) :
    Reads (Parse.parsePrimaryType (f + 1)) (.paren sp inner) FollowsPrimary := by
  intro s ts rest hs hl hk hn hr _
  -- The tokens are `(`, the tokens of `inner`, and `)`.
  have htok : (TypeExpr.paren sp inner).tokens = .punct "(" :: inner.tokens ++ [.punct ")"] := by
    simp [TypeExpr.tokens, TypeExpr.words, punctWord]
  rw [htok] at hk
  obtain ⟨lp, ts', rfl, hlp, hk'⟩ : ∃ lp ts', ts = lp :: ts' ∧ lp.kind = .punct "(" ∧
      ts'.map (·.kind) = inner.tokens ++ [.punct ")"] := by
    match ts, hk with
    | lp :: ts', hk => simp at hk; exact ⟨lp, ts', rfl, hk.1, hk.2⟩
  obtain ⟨its, rp, rfl, hits, hrp⟩ : ∃ its rp, ts' = its ++ [rp] ∧ its.map (·.kind) = inner.tokens ∧
      rp.kind = .punct ")" := by
    obtain ⟨its, rest', h1, h2, h3⟩ := List.map_eq_append_iff.mp hk'
    cases rest' with
    | nil => simp at h3
    | cons rp r2 =>
      cases r2 with
      | nil => simp at h3; exact ⟨its, rp, h1, h2, h3⟩
      | cons _ _ => simp at h3
  have hs1 : s.rest = lp :: (its ++ rp :: rest) := by simpa using hs
  let s₁ := { s with rest := its ++ rp :: rest, left := s.left - 1, lastStop := lp.span.stop }
  have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs1]
  obtain ⟨inner', s₂, hp, he, hL⟩ := h s₁ its (rp :: rest) rfl hl₁ hits
    (fun x hx => hn x (by simp [hx])) (by simp)
    ⟨⟨fun t ht => by simp at ht; subst ht; simp [hrp], fun t ht => by simp at ht; subst ht; simp [hrp]⟩,
     fun t ht => by simp at ht; subst ht; simp [hrp]⟩
  have hs2 : s₂.rest = rp :: rest := hL.rest_eq
  refine ⟨.paren ⟨lp.span.start, rp.span.stop⟩ inner',
    { s₂ with rest := rest, left := s₂.left - 1, lastStop := rp.span.stop }, ?_, ?_, ?_⟩
  · have hadv := Parse.advance_cons hs1 (by simp)
    simp only [Parse.parsePrimaryType, bind, EStateM.bind, hadv, hlp]
    simp only [show s₁ = { s with rest := its ++ rp :: rest, left := s.left - 1, lastStop := lp.span.stop } from rfl] at hp
    simp [hp, Parse.expectPunct_ok hs2 hr hrp, Parse.spanFrom, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, pure, EStateM.pure]
  · simp [TypeExpr.erase, he]
  · exact leaves_trans (leaves_advance hs1 hl) (leaves_trans hL (leaves_advance hs2 (by rw [hL.left_eq, hs2])))

/-! ### The array loop -/

/-- `t` with `k` array types around it. -/
def arrayOf (sp : Span) : Nat → TypeExpr → TypeExpr
  | 0, t => t
  | k + 1, t => .array sp (arrayOf sp k t)

/-- The tokens `[ ]`, `k` times. -/
def brackets : Nat → List TokenKind
  | 0 => []
  | k + 1 => .punct "[" :: .punct "]" :: brackets k

theorem arrayOf_array (sp : Span) (k : Nat) (t : TypeExpr) :
    arrayOf sp k (.array sp t) = .array sp (arrayOf sp k t) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [arrayOf, ih]

/-- The loop of `parseArrayType`, for any step that stops before a token other
than `[`, and reads `[ ]` as one more array type. -/
theorem iterate_brackets {step : TypeExpr → ParseM (TypeExpr × Bool)}
    (hstop : ∀ acc s u r, s.rest = u :: r → u.kind ≠ .punct "[" → step acc s = .ok (acc, false) s)
    (hgo : ∀ acc s lb rb r, s.rest = lb :: rb :: r → r ≠ [] → lb.kind = .punct "[" →
      rb.kind = .punct "]" → lb.newlineBefore = false →
      ∃ sp, step acc s = .ok (.array sp acc, true)
        { s with rest := r, left := s.left - 1 - 1, lastStop := rb.span.stop }) :
    ∀ (k fuel : Nat) (acc : TypeExpr) (s : ParseState) (ts rest : List Token), k < fuel →
      s.rest = ts ++ rest → s.left = s.rest.length → ts.map (·.kind) = brackets k →
      (∀ x ∈ ts, NoBreak x) → rest ≠ [] → FollowsArray rest →
      ∃ res s', Parse.iterate fuel acc step s = .ok res s' ∧ res.erase = arrayOf noSpan k acc.erase ∧
        Leaves s s' rest := by
  intro k
  induction k with
  | zero =>
    intro fuel acc s ts rest hk hs hl htk _ hr hf
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
    have hts : ts = [] := by simpa [brackets] using htk
    subst hts
    obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
    have hs' : s.rest = u :: r := by simpa using hs
    refine ⟨acc, s, ?_, rfl, Leaves.refl (by simpa using hs) (by simp [hl, hs'])⟩
    rw [Parse.iterate_succ]
    simp [bind, EStateM.bind, hstop acc s u r hs' (hf.2 u rfl), pure, EStateM.pure]
  | succ k ih =>
    intro fuel acc s ts rest hk hs hl htk hn hr hf
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨lb, rb, ts', rfl, hlb, hrb, htk'⟩ : ∃ lb rb ts', ts = lb :: rb :: ts' ∧
        lb.kind = .punct "[" ∧ rb.kind = .punct "]" ∧ ts'.map (·.kind) = brackets k := by
      cases ts with
      | nil => simp [brackets] at htk
      | cons lb ts₁ =>
        cases ts₁ with
        | nil => simp [brackets] at htk
        | cons rb ts' =>
          simp [brackets] at htk; exact ⟨lb, rb, ts', rfl, htk.1, htk.2.1, htk.2.2⟩
    have hs' : s.rest = lb :: rb :: (ts' ++ rest) := by simpa using hs
    obtain ⟨sp, hstep⟩ := hgo acc s lb rb (ts' ++ rest) hs' (by simp [hr])
      hlb hrb (noBreak_of hlb (by decide) (hn lb (by simp)))
    let s₂ := { s with rest := ts' ++ rest, left := s.left - 1 - 1, lastStop := rb.span.stop }
    have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, hl, hs']
    obtain ⟨res, s', hit, he, hL⟩ := ih f' (.array sp acc) s₂ ts' rest (by omega) rfl hl₂ htk'
      (fun x hx => hn x (by simp [hx])) hr hf
    refine ⟨res, s', ?_, ?_, ?_⟩
    · rw [Parse.iterate_succ]
      simp only [bind, EStateM.bind, hstep]
      exact hit
    · rw [he]; simp [TypeExpr.erase, arrayOf, arrayOf_array]
    · exact ⟨⟨hL.eof_eq, hL.inFunction_eq, hL.loopDepth_eq, hL.target_eq⟩, hL.rest_eq, hL.left_eq⟩

theorem brackets_succ (k : Nat) : brackets k ++ [.punct "[", .punct "]"] = brackets (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [brackets] at ih ⊢; exact ih

theorem length_brackets (k : Nat) : (brackets k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [brackets, ih]; omega

/-- A type that `parseArrayType` reads is a primary type with `k` array types
around it. -/
theorem arrayWF_split : ∀ (t : TypeExpr), t.arrayWF = true → ∃ (base : TypeExpr) (k : Nat), base.primaryWF = true ∧
    t.tokens = base.tokens ++ brackets k ∧ t.erase = arrayOf noSpan k base.erase ∧ base.height = t.height
  | .array sp elem, h => by
    obtain ⟨base, k, hb, ht, he, hh⟩ := arrayWF_split elem (by simpa [TypeExpr.arrayWF] using h)
    refine ⟨base, k + 1, hb, ?_, ?_, ?_⟩
    · simp [TypeExpr.tokens, TypeExpr.words, punctWord] at ht ⊢
      rw [ht, List.append_assoc, brackets_succ]
    · simp [TypeExpr.erase, arrayOf, he]
    · simp [TypeExpr.height, hh]
  | .keyword sp n, h => ⟨.keyword sp n, 0, by simpa [TypeExpr.arrayWF, TypeExpr.primaryWF] using h, by simp [brackets], rfl, rfl⟩
  | .null sp, _ => ⟨.null sp, 0, rfl, by simp [brackets], rfl, rfl⟩
  | .literal sp l, _ => ⟨.literal sp l, 0, rfl, by simp [brackets], rfl, rfl⟩
  | .ref sp n args, h => ⟨.ref sp n args, 0, by simpa [TypeExpr.arrayWF, TypeExpr.primaryWF] using h, by simp [brackets], rfl, rfl⟩
  | .paren sp i, h => ⟨.paren sp i, 0, by simpa [TypeExpr.arrayWF, TypeExpr.primaryWF] using h, by simp [brackets], rfl, rfl⟩
  | .union .., h => by simp [TypeExpr.arrayWF] at h

/-- `iterate_brackets`, in the shape of a goal about a parser that starts at
`s₀`, so that `refine` finds the step. -/
theorem iterate_brackets_goal {step : TypeExpr → ParseM (TypeExpr × Bool)}
    (hstop : ∀ acc s u r, s.rest = u :: r → u.kind ≠ .punct "[" → step acc s = .ok (acc, false) s)
    (hgo : ∀ acc s lb rb r, s.rest = lb :: rb :: r → r ≠ [] → lb.kind = .punct "[" →
      rb.kind = .punct "]" → lb.newlineBefore = false →
      ∃ sp, step acc s = .ok (.array sp acc, true)
        { s with rest := r, left := s.left - 1 - 1, lastStop := rb.span.stop })
    {k fuel : Nat} {acc target : TypeExpr} {s₀ s : ParseState} {ts rest : List Token} (hk : k < fuel)
    (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length) (hkind : ts.map (·.kind) = brackets k)
    (hn : ∀ x ∈ ts, NoBreak x) (hr : rest ≠ []) (hf : FollowsArray rest)
    (htarget : arrayOf noSpan k acc.erase = target.erase) (hL₀ : Leaves s₀ s (ts ++ rest)) :
    ∃ res s', Parse.iterate fuel acc step s = .ok res s' ∧ res.erase = target.erase ∧
      Leaves s₀ s' rest := by
  obtain ⟨res, s', hit, he, hL⟩ := iterate_brackets hstop hgo k fuel acc s ts rest hk hs hl hkind hn hr hf
  exact ⟨res, s', hit, he.trans htarget, leaves_trans hL₀ hL⟩

theorem Parse.budget_eq (s : ParseState) : Parse.budget s = .ok (10 * (s.left + 1)) s := by
  simp [Parse.budget, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]

/-- `parseArrayType` reads a type that `parsePrimaryType` reads, with `[ ]` after
it any number of times. -/
theorem parseArrayType_reads (f : Nat) (t : TypeExpr) (hwf : t.arrayWF = true)
    (hprim : ∀ b : TypeExpr, b.primaryWF = true → b.height = t.height →
      Reads (Parse.parsePrimaryType f) b FollowsPrimary) :
    Reads (Parse.parseArrayType (f + 1)) t FollowsArray := by
  intro s ts rest hs hl hk hn hr hf
  obtain ⟨base, k, hb, htok, he, hh⟩ := arrayWF_split t hwf
  rw [htok] at hk
  obtain ⟨bts, kts, rfl, hbk, hkk⟩ := List.map_eq_append_iff.mp hk
  obtain ⟨x0, r0, hs0⟩ : ∃ x0 r0, s.rest = x0 :: r0 := by
    cases h : s.rest with
    | nil => simp [h] at hs; exact absurd hs.2.2 hr
    | cons x0 r0 => exact ⟨x0, r0, rfl⟩
  -- The primary type, which `[` or the rest follows.
  have hfp : FollowsPrimary (kts ++ rest) := by
    intro x hx
    cases k with
    | zero =>
      have : kts = [] := by simpa [brackets] using hkk
      subst this; exact hf.1 x (by simpa using hx)
    | succ k =>
      cases kts with
      | nil => simp [brackets] at hkk
      | cons y kts' =>
        simp at hx; subst hx; simp [brackets] at hkk; simp [hkk.1]
  obtain ⟨base', s₁, hp, hbe, hL₁⟩ := hprim base hb hh s bts (kts ++ rest) (by simpa using hs) hl hbk
    (fun x hx => hn x (by simp [hx])) (by simp [hr]) hfp
  have hl₁ : s₁.left = s₁.rest.length := by rw [hL₁.left_eq, hL₁.rest_eq]
  have hk' : k < 10 * (s.left + 1) := by
    have := congrArg List.length hkk
    simp [length_brackets] at this
    rw [hl, hs]; simp; omega
  simp only [Parse.parseArrayType, bind, EStateM.bind, Parse.peek_eq hs0, Parse.budget_eq, hp]
  refine iterate_brackets_goal ?_ ?_ hk' hL₁.rest_eq hl₁ hkk (fun x hx => hn x (by simp [hx])) hr hf
    (by rw [hbe, he]) hL₁
  · intro acc s u r hsu hu
    simp [Parse.arrayStep, Parse.peek_eq hsu, Token.isPunct, hu, bind, EStateM.bind, pure, EStateM.pure]
  · intro acc s lb rb r hsr hr' hlb hrb hnl
    obtain ⟨u, r', rfl⟩ := List.exists_cons_of_ne_nil hr'
    refine ⟨⟨x0.span.start, rb.span.stop⟩, ?_⟩
    have h1 : s.rest[1]? = some rb := by simp [hsr]
    simp [Parse.arrayStep, Parse.peek_eq hsr, Parse.peekAt_eq h1, Token.isPunct, hlb, hrb, hnl, Parse.skip,
      Parse.advance_eq hsr, Parse.advance_eq (s := past s lb (rb :: (u :: r'))) rfl, Parse.spanFrom,
      discard, Functor.mapConst,
      EStateM.map, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]

/-! ### Lists with a separator -/

theorem eraseAll_append (xs ys : List TypeExpr) :
    TypeExpr.eraseAll (xs ++ ys) = TypeExpr.eraseAll xs ++ TypeExpr.eraseAll ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [TypeExpr.eraseAll, ih]

/-- The kinds of `items`' tokens, with a `sep` token between two of them. -/
def joined (sep : String) : List (List TokenKind) → List TokenKind
  | [] => []
  | [item] => item
  | item :: rest => item ++ .punct sep :: joined sep rest

/-- A loop that reads one item with `p` in each step, and goes on while a `sep`
token follows it. It reads items with `sep` between them, which a token other
than `sep` follows. -/
theorem iterate_sep {p : ParseM TypeExpr} {step : Array TypeExpr → ParseM (Array TypeExpr × Bool)}
    {sep : String} {follows : List Token → Prop}
    (hlast : ∀ acc s s' a u r, p s = .ok a s' → s'.rest = u :: r → u.kind ≠ .punct sep →
      step acc s = .ok (acc.push a, false) s')
    (hmore : ∀ acc s s' a c r, p s = .ok a s' → s'.rest = c :: r → r ≠ [] → c.kind = .punct sep →
      step acc s = .ok (acc.push a, true) { s' with rest := r, left := s'.left - 1, lastStop := c.span.stop })
    (hfollow : ∀ (c : Token) r, c.kind = .punct sep → follows (c :: r)) :
    ∀ (items : List TypeExpr) (fuel : Nat) (acc : Array TypeExpr) (s : ParseState) (ts rest : List Token),
      items ≠ [] → (∀ a ∈ items, Reads p a follows) → items.length ≤ fuel →
      s.rest = ts ++ rest → s.left = s.rest.length → ts.map (·.kind) = joined sep (items.map TypeExpr.tokens) →
      (∀ x ∈ ts, NoBreak x) → rest ≠ [] → follows rest →
      (∀ u ∈ rest.head?, u.kind ≠ .punct sep) →
      ∃ res s', Parse.iterate fuel acc step s = .ok res s' ∧
        TypeExpr.eraseAll res.toList = TypeExpr.eraseAll (acc.toList ++ items) ∧ Leaves s s' rest := by
  intro items
  induction items with
  | nil => intro _ _ _ _ _ h; exact absurd rfl h
  | cons a items ih =>
    intro fuel acc s ts rest _ hreads hlen hs hl hk hn hr hf hnot
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    cases items with
    | nil =>
      simp [joined] at hk
      obtain ⟨a', s', hp, he, hL⟩ := hreads a (by simp) s ts rest hs hl hk hn hr hf
      obtain ⟨u, r, hur⟩ := List.exists_cons_of_ne_nil hr
      have hs' : s'.rest = u :: r := by rw [hL.rest_eq, hur]
      have hu : u.kind ≠ .punct sep := hnot u (by simp [hur])
      refine ⟨acc.push a', s', ?_, ?_, hL⟩
      · rw [Parse.iterate_succ]
        simp [bind, EStateM.bind, hlast acc s s' a' u r hp hs' hu, pure, EStateM.pure]
      · simp [eraseAll_append, TypeExpr.eraseAll, he]
    | cons b items' =>
      have hk' : ts.map (·.kind) = a.tokens ++ .punct sep :: joined sep ((b :: items').map TypeExpr.tokens) := by
        simpa [joined] using hk
      obtain ⟨ats, rest₁, hts, hak, hrest₁⟩ := List.map_eq_append_iff.mp hk'
      obtain ⟨c, ts', rfl, hc, hts'⟩ : ∃ c ts', rest₁ = c :: ts' ∧ c.kind = .punct sep ∧
          ts'.map (·.kind) = joined sep ((b :: items').map TypeExpr.tokens) := by
        cases rest₁ with
        | nil => simp at hrest₁
        | cons c ts' => simp at hrest₁; exact ⟨c, ts', rfl, hrest₁.1, hrest₁.2⟩
      subst hts
      have hne : ts' ++ rest ≠ [] := by simp [hr]
      obtain ⟨a', s', hp, he, hL⟩ := hreads a (by simp) s ats (c :: (ts' ++ rest)) (by simpa using hs) hl hak
        (fun x hx => hn x (by simp [hx])) (by simp) (hfollow c _ hc)
      have hs' : s'.rest = c :: (ts' ++ rest) := hL.rest_eq
      let s₂ := { s' with rest := ts' ++ rest, left := s'.left - 1, lastStop := c.span.stop }
      have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, hL.left_eq]
      obtain ⟨res, s'', hit, he', hL'⟩ := ih f' (acc.push a') s₂ ts' rest (by simp)
        (fun x hx => hreads x (by simp [hx])) (by simp at hlen ⊢; omega) rfl hl₂ hts'
        (fun x hx => hn x (by simp [hx])) hr hf hnot
      refine ⟨res, s'', ?_, ?_, ?_⟩
      · rw [Parse.iterate_succ]
        simp only [bind, EStateM.bind, hmore acc s s' a' c (ts' ++ rest) hp hs' hne hc]
        exact hit
      · rw [he']; simp [eraseAll_append, TypeExpr.eraseAll, he]
      · exact leaves_trans hL (leaves_trans (leaves_advance hs' (by rw [hL.left_eq, hs'])) hL')

/-- A loop that, in each step, stops unless a `sep` token comes next, and else
reads the `sep` and one item with `p`. It reads items with a `sep` before each,
which a token other than `sep` follows. -/
theorem iterate_sepBefore {p : ParseM TypeExpr} {step : Array TypeExpr → ParseM (Array TypeExpr × Bool)}
    {sep : String} {follows : List Token → Prop}
    (hstop : ∀ acc s u r, s.rest = u :: r → u.kind ≠ .punct sep → step acc s = .ok (acc, false) s)
    (hgo : ∀ acc s s' a c r, s.rest = c :: r → r ≠ [] → c.kind = .punct sep →
      p { s with rest := r, left := s.left - 1, lastStop := c.span.stop } = .ok a s' →
      step acc s = .ok (acc.push a, true) s')
    (hfollow : ∀ (c : Token) r, c.kind = .punct sep → follows (c :: r)) :
    ∀ (items : List TypeExpr) (fuel : Nat) (acc : Array TypeExpr) (s : ParseState) (ts rest : List Token),
      (∀ a ∈ items, Reads p a follows) → items.length < fuel →
      s.rest = ts ++ rest → s.left = s.rest.length →
      ts.map (·.kind) = (items.map fun i => .punct sep :: i.tokens).flatten →
      (∀ x ∈ ts, NoBreak x) → rest ≠ [] → follows rest →
      (∀ u ∈ rest.head?, u.kind ≠ .punct sep) →
      ∃ res s', Parse.iterate fuel acc step s = .ok res s' ∧
        TypeExpr.eraseAll res.toList = TypeExpr.eraseAll (acc.toList ++ items) ∧ Leaves s s' rest := by
  intro items
  induction items with
  | nil =>
    intro fuel acc s ts rest _ hlen hs hl hk _ hr _ hnot
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    have hts : ts = [] := by simpa using hk
    subst hts
    obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
    have hs' : s.rest = u :: r := by simpa using hs
    refine ⟨acc, s, ?_, by simp, Leaves.refl (by simpa using hs) (by simp [hl, hs'])⟩
    rw [Parse.iterate_succ]
    simp [bind, EStateM.bind, hstop acc s u r hs' (hnot u rfl), pure, EStateM.pure]
  | cons a items ih =>
    intro fuel acc s ts rest hreads hlen hs hl hk hn hr hf hnot
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    obtain ⟨c, ts₁, rfl, hc, hk₁⟩ : ∃ c ts₁, ts = c :: ts₁ ∧ c.kind = .punct sep ∧
        ts₁.map (·.kind) = a.tokens ++ (items.map fun i => .punct sep :: i.tokens).flatten := by
      cases ts with
      | nil => simp at hk
      | cons c ts₁ => simp at hk; exact ⟨c, ts₁, rfl, hk.1, hk.2⟩
    obtain ⟨ats, its, rfl, hak, hik⟩ := List.map_eq_append_iff.mp hk₁
    have hs' : s.rest = c :: (ats ++ (its ++ rest)) := by simpa using hs
    let s₁ := { s with rest := ats ++ (its ++ rest), left := s.left - 1, lastStop := c.span.stop }
    have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs']
    -- The item, which a `sep` or the rest follows.
    have hfa : follows (its ++ rest) := by
      cases items with
      | nil => have : its = [] := by simpa using hik
               subst this; simpa using hf
      | cons i items' =>
        cases its with
        | nil => simp at hik
        | cons d its' => simp at hik; exact hfollow d _ hik.1
    obtain ⟨a', s', hp, he, hL⟩ := hreads a (by simp) s₁ ats (its ++ rest) rfl hl₁ hak
      (fun x hx => hn x (by simp [hx])) (by simp [hr]) hfa
    have hl' : s'.left = s'.rest.length := by rw [hL.left_eq, hL.rest_eq]
    obtain ⟨res, s'', hit, he', hL'⟩ := ih f' (acc.push a') s' its rest
      (fun x hx => hreads x (by simp [hx])) (by simp at hlen ⊢; omega) hL.rest_eq hl' hik
      (fun x hx => hn x (by simp [hx])) hr hf hnot
    refine ⟨res, s'', ?_, ?_, ?_⟩
    · rw [Parse.iterate_succ]
      simp only [bind, EStateM.bind, hgo acc s s' a' c (ats ++ (its ++ rest)) hs' (by simp [hr]) hc hp]
      exact hit
    · rw [he']; simp [eraseAll_append, TypeExpr.eraseAll, he]
    · exact leaves_trans (leaves_advance hs' hl) (leaves_trans hL hL')

/-! ### Tokens of lists -/

theorem wordsOf_eq (ts : List TypeExpr) : TypeExpr.wordsOf ts = ts.map TypeExpr.words := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [TypeExpr.wordsOf, ih]

theorem separated_flatten (sep : String) (items : List (List Word)) :
    (separated sep items).flatten = joined sep (items.map List.flatten) := by
  induction items with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp [separated, joined]
    | cons y ys => simp [separated, joined, punctWord] at ih ⊢; rw [ih]

theorem joined_cons (sep : String) (x : List TokenKind) (xs : List (List TokenKind)) :
    joined sep (x :: xs) = x ++ (xs.map fun i => .punct sep :: i).flatten := by
  induction xs generalizing x with
  | nil => simp [joined]
  | cons y ys ih => simp [joined, ih]

theorem tokens_ref (sp : Span) (name : String) (args : List TypeExpr) (h : args ≠ []) :
    (TypeExpr.ref sp name args).tokens =
      .ident name :: .punct "<" :: joined "," (args.map TypeExpr.tokens) ++ [.punct ">"] := by
  cases args with
  | nil => exact absurd rfl h
  | cons a as =>
    simp only [TypeExpr.tokens, TypeExpr.words, identWord, punctWord, List.flatten_cons,
      List.flatten_append]
    rw [separated_flatten, wordsOf_eq]
    simp [List.map_map, Function.comp_def, TypeExpr.tokens]
    rfl

theorem followsType_cons {u : Token} {r : List Token} (h1 : u.kind ≠ .punct "<") (h2 : u.kind ≠ .punct ".")
    (h3 : u.kind ≠ .punct "[") (h4 : u.kind ≠ .punct "|") (h5 : u.kind ≠ .punct "&") :
    FollowsType (u :: r) :=
  ⟨⟨fun t ht => by simp at ht; subst ht; exact ⟨h1, h2⟩, fun t ht => by simp at ht; subst ht; exact h3⟩,
    fun t ht => by simp at ht; subst ht; exact ⟨h4, h5⟩⟩

theorem punct_ne {a b : String} (h : a ≠ b) : TokenKind.punct a ≠ TokenKind.punct b := by
  intro e; injection e with e; exact h e

/-- A `p` token may follow a type, unless `p` would continue it. -/
theorem followsType_punct {u : Token} {r : List Token} {p : String} (hu : u.kind = .punct p)
    (h : p ∉ ["<", ".", "[", "|", "&"]) : FollowsType (u :: r) := by
  simp at h
  exact followsType_cons (by rw [hu]; exact punct_ne h.1) (by rw [hu]; exact punct_ne h.2.1)
    (by rw [hu]; exact punct_ne h.2.2.1) (by rw [hu]; exact punct_ne h.2.2.2.1)
    (by rw [hu]; exact punct_ne h.2.2.2.2)

theorem length_joined (sep : String) (xs : List (List TokenKind)) :
    xs.length ≤ (joined sep xs).length + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp [joined]
    | cons y ys => simp [joined] at ih ⊢; omega

/-- `Name < A , B >`, when `parseType` reads each argument. -/
theorem parsePrimaryType_ref (f : Nat) (sp : Span) (name : String) (args : List TypeExpr)
    (hname : typeName name = true) (hargs : args ≠ [])
    (h : ∀ a ∈ args, Reads (Parse.parseType f) a FollowsType) :
    Reads (Parse.parsePrimaryType (f + 1)) (.ref sp name args) FollowsPrimary := by
  intro s ts rest hs hl hk hn hr _
  rw [tokens_ref sp name args hargs] at hk
  obtain ⟨x, lt, ts₁, rfl, hx, hlt, hk₁⟩ : ∃ x lt ts₁, ts = x :: lt :: ts₁ ∧ x.kind = .ident name ∧
      lt.kind = .punct "<" ∧ ts₁.map (·.kind) = joined "," (args.map TypeExpr.tokens) ++ [.punct ">"] := by
    cases ts with
    | nil => simp at hk
    | cons x ts =>
      cases ts with
      | nil => simp at hk
      | cons lt ts₁ => simp at hk; exact ⟨x, lt, ts₁, rfl, hk.1, hk.2.1, hk.2.2⟩
  obtain ⟨ats, rest₁, rfl, hak, hrest₁⟩ := List.map_eq_append_iff.mp hk₁
  obtain ⟨gt, rfl, hgt⟩ : ∃ gt, rest₁ = [gt] ∧ gt.kind = .punct ">" := by
    cases rest₁ with
    | nil => simp at hrest₁
    | cons gt r₂ =>
      cases r₂ with
      | nil => simp at hrest₁; exact ⟨gt, rfl, hrest₁⟩
      | cons _ _ => simp at hrest₁
  have hname' : (name ∉ Parse.keywordTypes ∧ name ∉ Parse.typeOperatorWords) ∧ name ∉ Parse.refusedNames := by
    simpa [typeName] using hname
  have hs₀ : s.rest = x :: lt :: (ats ++ gt :: rest) := by simpa using hs
  let s₁ := past s x (lt :: (ats ++ gt :: rest))
  have hs₁ : s₁.rest = lt :: (ats ++ gt :: rest) := rfl
  let s₂ := { s₁ with rest := ats ++ gt :: rest, left := s₁.left - 1, lastStop := lt.span.stop }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁, hl, hs₀]
  -- The arguments, which `>` follows.
  have hfg : FollowsType (gt :: rest) := followsType_punct hgt (by decide)
  obtain ⟨res, s₃, hit, he, hL⟩ := iterate_sep (p := Parse.parseType f) (sep := ",") (follows := FollowsType)
    (step := Parse.typeArgStep (Parse.parseType f))
    (fun acc s s' a u r hp hu hne => by
      simp [Parse.typeArgStep, bind, EStateM.bind, hp, Parse.peek_eq hu, Token.isPunct, hne, pure, EStateM.pure])
    (fun acc s s' a c r hp hc hr hck => by
      simp [Parse.typeArgStep, bind, EStateM.bind, hp, Parse.peek_eq hc, Token.isPunct, hck, Parse.advance_cons hc hr, discard,
        Functor.mapConst, EStateM.map, pure, EStateM.pure])
    (fun c r hc => followsType_punct hc (by decide))
    args (10 * (s₂.left + 1)) #[] s₂ ats (gt :: rest) hargs h
    (by
      have h1 := congrArg List.length hak
      have h2 := length_joined "," (args.map TypeExpr.tokens)
      simp at h1 h2
      simp [s₂, s₁, hl, hs₀]; omega)
    rfl hl₂ hak (fun y hy => hn y (by simp [hy])) (by simp) hfg
    (fun u hu => by simp at hu; subst hu; rw [hgt]; exact punct_ne (by decide))
  have hs₃ : s₃.rest = gt :: rest := hL.rest_eq
  have hltd : lt.kind ≠ .punct "." := by rw [hlt]; exact punct_ne (by decide)
  have hltn : lt.newlineBefore = false := noBreak_of hlt (by decide) (hn lt (by simp))
  refine ⟨.ref ⟨x.span.start, gt.span.stop⟩ name res.toList,
    { s₃ with rest := rest, left := s₃.left - 1, lastStop := gt.span.stop }, ?_, ?_, ?_⟩
  · simp only [s₂, s₁] at hit
    simp only [Parse.parsePrimaryType, bind, EStateM.bind, Parse.advance_eq hs₀, hx]
    simp [Parse.peek_eq (s := past s x (lt :: (ats ++ gt :: rest))) rfl, Token.isPunct, hlt, hltn,
      hname'.1.1, hname'.1.2, hname'.2,
      Parse.advance_cons (s := past s x (lt :: (ats ++ gt :: rest))) rfl (by simp), discard,
      Functor.mapConst, EStateM.map, Parse.budget_eq, hit, Parse.expectPunct_ok hs₃ hr hgt,
      Parse.spanFrom, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  · have he₂ : TypeExpr.eraseAll res.toList = TypeExpr.eraseAll args := by simpa using he
    simp [TypeExpr.erase, he₂]
  · exact leaves_trans (leaves_advance hs₀ hl)
      (leaves_trans (leaves_advance (s := past s x (lt :: (ats ++ gt :: rest))) rfl (by simp [hl, hs₀]))
        (leaves_trans hL (leaves_advance hs₃ (by rw [hL.left_eq, hs₃]))))

/-! ### Unions -/

/-- A type that `parseArrayType` reads has tokens, and the first is not `|`. -/
theorem arrayWF_head (t : TypeExpr) (h : t.arrayWF = true) :
    t.tokens ≠ [] ∧ ∀ k ∈ t.tokens.head?, k ≠ .punct "|" := by
  obtain ⟨base, k, hb, htok, _, _⟩ := arrayWF_split t h
  rw [htok]
  cases base with
  | keyword sp name =>
    simp only [TypeExpr.tokens, TypeExpr.words, keywordWord, identWord]
    split <;> simp
  | null sp => simp [TypeExpr.tokens, TypeExpr.words, keywordWord]
  | literal sp lit => cases lit <;> simp [TypeExpr.tokens, TypeExpr.words, LitType.words, keywordWord]
  | ref sp name args =>
    cases args <;> simp [TypeExpr.tokens, TypeExpr.words, identWord]
  | paren sp inner =>
    simp only [TypeExpr.tokens, TypeExpr.words, punctWord]
    refine ⟨by simp, fun k hk => ?_⟩
    simp at hk; subst hk; exact punct_ne (by decide)
  | array sp e => simp [TypeExpr.primaryWF] at hb
  | union sp ms => simp [TypeExpr.primaryWF] at hb

theorem unionStep_stop (p : ParseM TypeExpr) (acc : Array TypeExpr) (s : ParseState) (u : Token)
    (r : List Token) (hs : s.rest = u :: r) (hu : u.kind ≠ .punct "|") :
    Parse.unionStep p acc s = .ok (acc, false) s := by
  simp [Parse.unionStep, Parse.peek_eq hs, Token.isPunct, hu, bind, EStateM.bind, pure, EStateM.pure]

theorem unionStep_go (p : ParseM TypeExpr) (acc : Array TypeExpr) (s s' : ParseState) (a : TypeExpr)
    (c : Token) (r : List Token) (hs : s.rest = c :: r) (hr : r ≠ []) (hc : c.kind = .punct "|")
    (hp : p { s with rest := r, left := s.left - 1, lastStop := c.span.stop } = .ok a s') :
    Parse.unionStep p acc s = .ok (acc.push a, true) s' := by
  simp [Parse.unionStep, Parse.peek_eq hs, Token.isPunct, hc, Parse.advance_cons hs hr, discard,
    Functor.mapConst, EStateM.map, hp, bind, EStateM.bind, pure, EStateM.pure]

theorem iterate_stop {σ : Type} {step : σ → ParseM (σ × Bool)} {acc : σ} {s : ParseState} {fuel : Nat}
    (h : step acc s = .ok (acc, false) s) (hf : 0 < fuel) : Parse.iterate fuel acc step s = .ok acc s := by
  obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
  rw [Parse.iterate_succ]
  simp [bind, EStateM.bind, h, pure, EStateM.pure]

/-- `parseType` reads a type that `parseArrayType` reads, when no `|` follows. -/
theorem parseType_plain (f : Nat) (t : TypeExpr) (hwf : t.arrayWF = true)
    (harr : Reads (Parse.parseArrayType f) t FollowsArray) :
    Reads (Parse.parseType (f + 1)) t FollowsType := by
  intro s ts rest hs hl hk hn hr hf
  obtain ⟨hne, hhead⟩ := arrayWF_head t hwf
  obtain ⟨x0, ts₀, rfl⟩ : ∃ x0 ts₀, ts = x0 :: ts₀ := by
    cases ts with
    | nil => rw [← hk] at hne; simp at hne
    | cons x0 ts₀ => exact ⟨x0, ts₀, rfl⟩
  have hx0 : x0.kind ≠ .punct "|" := by
    have := hhead x0.kind; rw [← hk] at this; simpa using this
  have hs0 : s.rest = x0 :: (ts₀ ++ rest) := by simpa using hs
  obtain ⟨first, s₁, hp, he, hL⟩ := harr s (x0 :: ts₀) rest hs hl hk hn hr hf.1
  obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  have hs₁ : s₁.rest = u :: r := hL.rest_eq
  have hu : u.kind ≠ .punct "|" := (hf.2 u rfl).1
  have hamp : u.kind ≠ .punct "&" := (hf.2 u rfl).2
  refine ⟨first, s₁, ?_, he, hL⟩
  simp [Parse.parseType, Parse.peek_eq hs0, Token.isPunct, hx0, hp, Parse.budget_eq,
    iterate_stop (fuel := 10 * (s₁.left + 1)) (unionStep_stop _ #[first] s₁ u r hs₁ hu) (by omega),
    Parse.peek_eq hs₁, hamp,
    bind, EStateM.bind, pure, EStateM.pure]

/-- A `p` token may follow a type that `parseArrayType` reads, unless `p` would
continue it. -/
theorem followsArray_punct {u : Token} {r : List Token} {p : String} (hu : u.kind = .punct p)
    (h : p ∉ ["<", ".", "["]) : FollowsArray (u :: r) := by
  simp at h
  exact ⟨fun t ht => by simp at ht; subst ht; rw [hu]; exact ⟨punct_ne h.1, punct_ne h.2.1⟩,
    fun t ht => by simp at ht; subst ht; rw [hu]; exact punct_ne h.2.2⟩

theorem length_sepBefore (sep : String) (items : List TypeExpr) :
    items.length ≤ ((items.map fun i => .punct sep :: i.tokens).flatten).length := by
  induction items with
  | nil => simp
  | cons i is ih => simp at ih ⊢; omega

theorem allArrayWF_iff (ms : List TypeExpr) : TypeExpr.allArrayWF ms = true ↔ ∀ m ∈ ms, m.arrayWF = true := by
  induction ms with
  | nil => simp [TypeExpr.allArrayWF]
  | cons m ms ih => simp [TypeExpr.allArrayWF, ih]

theorem length_eraseAll (ms : List TypeExpr) : (TypeExpr.eraseAll ms).length = ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [TypeExpr.eraseAll, ih]

theorem tokens_union_one (sp : Span) (m : TypeExpr) :
    (TypeExpr.union sp [m]).tokens = .punct "|" :: m.tokens := by
  simp [TypeExpr.tokens, TypeExpr.words, punctWord]

theorem tokens_union (sp : Span) (m₁ m₂ : TypeExpr) (ms : List TypeExpr) :
    (TypeExpr.union sp (m₁ :: m₂ :: ms)).tokens =
      m₁.tokens ++ ((m₂ :: ms).map fun i => .punct "|" :: i.tokens).flatten := by
  simp only [TypeExpr.tokens, TypeExpr.words]
  rw [separated_flatten, wordsOf_eq, List.map_map]
  simp only [Function.comp_def, List.map_cons]
  rw [joined_cons]
  simp [List.map_map, Function.comp_def]

/-- `parseType` reads a union. -/
theorem parseType_union (f : Nat) (sp : Span) (ms : List TypeExpr) (hwf : (TypeExpr.union sp ms).wf = true)
    (harr : ∀ m ∈ ms, Reads (Parse.parseArrayType f) m FollowsArray) :
    Reads (Parse.parseType (f + 1)) (.union sp ms) FollowsType := by
  intro s ts rest hs hl hk hn hr hf
  obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  have hu : u.kind ≠ .punct "|" := (hf.2 u rfl).1
  have hamp : u.kind ≠ .punct "&" := (hf.2 u rfl).2
  match ms, hwf, harr with
  | [], hwf, _ => simp [TypeExpr.wf] at hwf
  | [m], hwf, harr =>
    rw [tokens_union_one] at hk
    obtain ⟨bar, mts, rfl, hbar, hmk⟩ : ∃ bar mts, ts = bar :: mts ∧ bar.kind = .punct "|" ∧
        mts.map (·.kind) = m.tokens := by
      cases ts with
      | nil => simp at hk
      | cons bar mts => simp at hk; exact ⟨bar, mts, rfl, hk.1, hk.2⟩
    have hs0 : s.rest = bar :: (mts ++ u :: r) := by simpa using hs
    have hne : mts ++ u :: r ≠ [] := by simp
    let s₀ := { s with rest := mts ++ u :: r, left := s.left - 1, lastStop := bar.span.stop }
    have hl₀ : s₀.left = s₀.rest.length := by simp [s₀, hl, hs0]
    obtain ⟨first, s₁, hp, he, hL⟩ := harr m (by simp) s₀ mts (u :: r) rfl hl₀ hmk
      (fun x hx => hn x (by simp [hx])) (by simp) hf.1
    have hs₁ : s₁.rest = u :: r := hL.rest_eq
    simp only [s₀] at hp
    refine ⟨.union ⟨bar.span.start, s₁.lastStop⟩ [first], s₁, ?_, ?_,
      leaves_trans (leaves_advance hs0 hl) hL⟩
    · simp [Parse.parseType, Parse.peek_eq hs0, Token.isPunct, hbar, Parse.advance_cons hs0 hne, discard,
        Functor.mapConst, EStateM.map, hp, Parse.budget_eq,
        iterate_stop (fuel := 10 * (s₁.left + 1)) (unionStep_stop _ #[first] s₁ u r hs₁ hu) (by omega),
        Parse.peek_eq hs₁, hamp, Parse.spanFrom, get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, pure, EStateM.pure]
    · simp [TypeExpr.erase, TypeExpr.eraseAll, he]
  | m₁ :: m₂ :: ms', hwf, harr =>
    have hall : ∀ m ∈ m₁ :: m₂ :: ms', m.arrayWF = true := by
      simp only [TypeExpr.wf] at hwf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
      exact (allArrayWF_iff _).mp hwf.2
    rw [tokens_union] at hk
    obtain ⟨ts₁, ts₂, rfl, hk₁, hk₂⟩ := List.map_eq_append_iff.mp hk
    obtain ⟨hne₁, hhead⟩ := arrayWF_head m₁ (hall m₁ (by simp))
    obtain ⟨x0, ts₁', rfl⟩ : ∃ x0 ts₁', ts₁ = x0 :: ts₁' := by
      cases ts₁ with
      | nil => rw [← hk₁] at hne₁; simp at hne₁
      | cons x0 ts₁' => exact ⟨x0, ts₁', rfl⟩
    have hx0 : x0.kind ≠ .punct "|" := by
      have := hhead x0.kind; rw [← hk₁] at this; simpa using this
    have hs0 : s.rest = x0 :: (ts₁' ++ (ts₂ ++ u :: r)) := by simpa using hs
    -- The first member, which a `|` follows.
    obtain ⟨bar, ts₂', rfl, hbar⟩ : ∃ bar ts₂', ts₂ = bar :: ts₂' ∧ bar.kind = .punct "|" := by
      cases ts₂ with
      | nil => simp at hk₂
      | cons bar ts₂' => simp at hk₂; exact ⟨bar, ts₂', rfl, hk₂.1⟩
    have hfa : FollowsArray (bar :: (ts₂' ++ u :: r)) := followsArray_punct hbar (by decide)
    obtain ⟨first, s₁, hp, he, hL⟩ := harr m₁ (by simp) s (x0 :: ts₁') (bar :: ts₂' ++ u :: r)
      (by simpa using hs) hl hk₁ (fun x hx => hn x (List.mem_append_left _ hx)) (by simp) (by simpa using hfa)
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL.left_eq, hL.rest_eq]
    have hcount : (m₂ :: ms').length < 10 * (s₁.left + 1) := by
      have h1 := congrArg List.length hk₂
      have h2 := length_sepBefore "|" (m₂ :: ms')
      rw [List.length_map] at h1
      rw [hl₁, hL.rest_eq]; simp at h1 h2 ⊢; omega
    obtain ⟨res, s₂, hit, hre, hL₂⟩ := iterate_sepBefore (p := Parse.parseArrayType f) (sep := "|")
      (follows := FollowsArray) (step := Parse.unionStep (Parse.parseArrayType f))
      (fun acc s u r hs hu => unionStep_stop _ acc s u r hs hu)
      (fun acc s s' a c r hs hr hc hp => unionStep_go _ acc s s' a c r hs hr hc hp)
      (fun c r hc => followsArray_punct hc (by decide))
      (m₂ :: ms') (10 * (s₁.left + 1)) #[first] s₁ (bar :: ts₂') (u :: r)
      (fun x hx => harr x (List.mem_cons_of_mem _ hx)) hcount (by simpa using hL.rest_eq) hl₁
      (by simpa using hk₂) (fun x hx => hn x (by simp [hx])) (by simp) hf.1 (fun x hx => by simp at hx; subst hx; exact hu)
    have hs₂ : s₂.rest = u :: r := hL₂.rest_eq
    have hsize : 1 < res.size := by
      have := congrArg List.length hre
      rw [length_eraseAll, length_eraseAll] at this
      simp at this; omega
    refine ⟨.union ⟨x0.span.start, s₂.lastStop⟩ res.toList, s₂, ?_, ?_, leaves_trans hL hL₂⟩
    · simp [Parse.parseType, Parse.peek_eq hs0, Token.isPunct, hx0, hp, Parse.budget_eq, hit,
        Parse.peek_eq hs₂, hamp, hsize, Parse.spanFrom, get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, pure, EStateM.pure]
    · simp [TypeExpr.erase, hre, TypeExpr.eraseAll, he]

/-! ### Every type -/

theorem height_le_heightOf {m : TypeExpr} {ms : List TypeExpr} (h : m ∈ ms) :
    m.height ≤ TypeExpr.heightOf ms := by
  induction ms with
  | nil => simp at h
  | cons x xs ih =>
    simp at h
    rcases h with rfl | h
    · simp only [TypeExpr.heightOf]; exact Nat.le_max_left _ _
    · have := ih h; simp only [TypeExpr.heightOf]; exact Nat.le_trans this (Nat.le_max_right _ _)

theorem allWF_iff (ms : List TypeExpr) : TypeExpr.allWF ms = true ↔ ∀ m ∈ ms, m.wf = true := by
  induction ms with
  | nil => simp [TypeExpr.allWF]
  | cons m ms ih => simp [TypeExpr.allWF, ih]

/-- The parser reads the tokens of every well-formed type as that type, given
fuel for how deep the type nests. `types_give` proves that every type the
parser gives is well formed. -/
theorem types_reads : ∀ f : Nat,
    (∀ t : TypeExpr, t.wf = true → 3 * t.height + 3 ≤ f → Reads (Parse.parseType f) t FollowsType) ∧
    (∀ t : TypeExpr, t.arrayWF = true → 3 * t.height + 2 ≤ f →
      Reads (Parse.parseArrayType f) t FollowsArray) ∧
    (∀ t : TypeExpr, t.primaryWF = true → 3 * t.height + 1 ≤ f →
      Reads (Parse.parsePrimaryType f) t FollowsPrimary)
  | 0 => ⟨fun _ _ h => by omega, fun _ _ h => by omega, fun _ _ h => by omega⟩
  | f + 1 => by
    obtain ⟨ihT, ihA, ihP⟩ := types_reads f
    refine ⟨?_, ?_, ?_⟩
    · intro t hwf hf
      cases t with
      | union sp ms =>
        refine parseType_union f sp ms hwf fun m hm => ihA m ?_ ?_
        · match ms, hwf, hm with
          | [m'], hwf, hm => simp at hm; subst hm; simpa [TypeExpr.wf] using hwf
          | m₁ :: m₂ :: ms', hwf, hm =>
            simp only [TypeExpr.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
            exact (allArrayWF_iff _).mp hwf.2 m hm
        · have := height_le_heightOf hm; simp [TypeExpr.height] at hf; omega
      | keyword sp n =>
        exact parseType_plain f _ (by simpa [TypeExpr.wf, TypeExpr.arrayWF] using hwf)
          (ihA _ (by simpa [TypeExpr.wf, TypeExpr.arrayWF] using hwf) (by simp [TypeExpr.height] at hf ⊢; omega))
      | null sp => exact parseType_plain f _ rfl (ihA _ rfl (by simp [TypeExpr.height] at hf ⊢; omega))
      | literal sp l => exact parseType_plain f _ rfl (ihA _ rfl (by simp [TypeExpr.height] at hf ⊢; omega))
      | ref sp n args =>
        exact parseType_plain f _ (by simpa [TypeExpr.wf, TypeExpr.arrayWF] using hwf)
          (ihA _ (by simpa [TypeExpr.wf, TypeExpr.arrayWF] using hwf) (by omega))
      | array sp e =>
        exact parseType_plain f _ (by simpa [TypeExpr.wf, TypeExpr.arrayWF] using hwf)
          (ihA _ (by simpa [TypeExpr.wf, TypeExpr.arrayWF] using hwf) (by omega))
      | paren sp i =>
        exact parseType_plain f _ (by simpa [TypeExpr.wf, TypeExpr.arrayWF] using hwf)
          (ihA _ (by simpa [TypeExpr.wf, TypeExpr.arrayWF] using hwf) (by omega))
    · intro t hwf hf
      exact parseArrayType_reads f t hwf fun b hb hh => ihP b hb (by omega)
    · intro t hwf hf
      cases t with
      | keyword sp name =>
        by_cases hv : name = "void"
        · subst hv
          exact reads_one (k := .keyword "void") (expected := fun x => .keyword x.span "void")
            (by simp [TypeExpr.tokens, TypeExpr.words, keywordWord]) (fun x => rfl)
            fun s x u r hs hx _ => parsePrimaryType_simple f s x u r _ hs (by simp [simpleType, hx])
        · have hk : name ∈ Parse.keywordTypes := by simpa [TypeExpr.primaryWF, hv] using hwf
          exact reads_one (k := .ident name) (expected := fun x => .keyword x.span name)
            (by simp [TypeExpr.tokens, TypeExpr.words, identWord, hv]) (fun x => rfl)
            fun s x u r hs hx hu => parsePrimaryType_keyword f s x u r name hs hx hu hk
      | null sp =>
        exact reads_one (k := .keyword "null") (expected := fun x => .null x.span)
          (by simp [TypeExpr.tokens, TypeExpr.words, keywordWord]) (fun x => rfl)
          fun s x u r hs hx _ => parsePrimaryType_simple f s x u r _ hs (by simp [simpleType, hx])
      | literal sp lit =>
        cases lit with
        | string v =>
          exact reads_one (k := .string v) (expected := fun x => .literal x.span (.string v))
            (by simp [TypeExpr.tokens, TypeExpr.words, LitType.words]) (fun x => rfl)
            fun s x u r hs hx _ => parsePrimaryType_simple f s x u r _ hs (by simp [simpleType, hx])
        | number t =>
          exact reads_one (k := .number t) (expected := fun x => .literal x.span (.number t))
            (by simp [TypeExpr.tokens, TypeExpr.words, LitType.words]) (fun x => rfl)
            fun s x u r hs hx _ => parsePrimaryType_simple f s x u r _ hs (by simp [simpleType, hx])
        | bigint t =>
          exact reads_one (k := .bigint t) (expected := fun x => .literal x.span (.bigint t))
            (by simp [TypeExpr.tokens, TypeExpr.words, LitType.words]) (fun x => rfl)
            fun s x u r hs hx _ => parsePrimaryType_simple f s x u r _ hs (by simp [simpleType, hx])
        | bool b =>
          cases b with
          | true =>
            exact reads_one (k := .keyword "true") (expected := fun x => .literal x.span (.bool true))
              (by simp [TypeExpr.tokens, TypeExpr.words, LitType.words, keywordWord]) (fun x => rfl)
              fun s x u r hs hx _ => parsePrimaryType_simple f s x u r _ hs (by simp [simpleType, hx])
          | false =>
            exact reads_one (k := .keyword "false") (expected := fun x => .literal x.span (.bool false))
              (by simp [TypeExpr.tokens, TypeExpr.words, LitType.words, keywordWord]) (fun x => rfl)
              fun s x u r hs hx _ => parsePrimaryType_simple f s x u r _ hs (by simp [simpleType, hx])
      | ref sp name args =>
        have hname : typeName name = true := by
          simp only [TypeExpr.primaryWF, Bool.and_eq_true] at hwf; exact hwf.1
        cases args with
        | nil =>
          exact reads_one (k := .ident name) (expected := fun x => .ref x.span name [])
            (by simp [TypeExpr.tokens, TypeExpr.words, identWord]) (fun x => rfl)
            fun s x u r hs hx hu => parsePrimaryType_name f s x u r name hs hx hu hname
        | cons a as =>
          have hall : ∀ m ∈ a :: as, m.wf = true := by
            simp only [TypeExpr.primaryWF, Bool.and_eq_true] at hwf; exact (allWF_iff _).mp hwf.2
          exact parsePrimaryType_ref f sp name (a :: as) hname (by simp) fun m hm =>
            ihT m (hall m hm) (by have := height_le_heightOf hm; simp [TypeExpr.height] at hf; omega)
      | paren sp inner =>
        exact parsePrimaryType_paren f sp inner
          (ihT inner (by simpa [TypeExpr.primaryWF] using hwf) (by simp [TypeExpr.height] at hf; omega))
      | array sp e => simp [TypeExpr.primaryWF] at hwf
      | union sp ms => simp [TypeExpr.primaryWF] at hwf

end tolean.TypeScript.Syntax
