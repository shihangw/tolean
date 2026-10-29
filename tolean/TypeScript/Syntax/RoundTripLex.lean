import tolean.TypeScript.Syntax.RoundTripDecl

/-!
The parser's round trip, the lexer's part: the lexer reads the source that
`render` writes for some lines of words as the tokens that `Laid` describes,
followed by the end of the file.

`Word.ok T w` states which words the lexer reads back for the target `T`. A
word can be a `lineBreak`, one token that `TokenKind.ok` accepts, or a `>`
that touches the rest of the word, as in `>=`. A number or a bigint is
accepted when `lexNumber` reads its text, followed by a space, as the same
token. `lexChars_ok_kinds` proves that every token the lexer gives, apart from
the end of the file, is a word of this kind. So `Word.ok` accepts exactly the
tokens that the lexer can give.

`lexChars_render` also needs each line break inside a line to come right
before a `(` (`breaksOK`). The printer puts one only between `async` and the
`(` of a call of it. `Laid` allows a line break inside a line only before a
`(`, so a line break before another word would make the theorem false.

Most functions of the lexer read a printed token along one path, and the
proofs step through that path. `lexNumber` has many paths. So `lexNumber_eq`
states it as a function on a list of characters, `numberOf`, and
`numberOf_frame` shows that a number reads the same when a space follows it
instead of the character that followed it in the source. `Keeps` states what
every function of the lexer keeps, such as the tokens read so far, and the
tactic `keeps` proves it by stepping through the code of a function.
-/
namespace tolean.TypeScript.Syntax

open tolean

-- The proofs step through the lexer with one set of lemmas, so some pass a
-- lemma that their step does not use.
set_option linter.unusedSimpArgs false

/-! ### The words that the lexer reads back -/

/-- A name that the lexer reads as one identifier or keyword: an ASCII letter, `_` or `$`, then any
number of letters, digits, `_` and `$`. -/
def identName (n : String) : Bool :=
  match n.toList with
  | c :: cs => Lex.isIdentStart c && cs.all Lex.isIdentPart
  | [] => false

/-- `lexKind` gives the characters `cs` to `lexNumber`: they start with a digit, or with a `.` before a
digit. -/
def startsNumber : List Char → Bool
  | c :: cs => c.isDigit || (c == '.' && cs.head?.any Char.isDigit)
  | [] => false

/-- The lexer reads the text of `k`, followed by a space, as the number or bigint `k`. Every number that
the lexer gives passes this test (`lexChars_ok_kinds`), and the lexer reads every number that passes it
(`lexKind_number`). -/
def numberOK (T : Edition) (k : TokenKind) : Bool :=
  let cs := k.text.toList ++ [' ']
  startsNumber cs &&
    match Lex.lexNumber ⟨1, 1⟩ { rest := cs, size := cs.length, target := T } with
    | .ok k' s => k' == k && s.rest == [' ']
    | .error _ _ => false

/-- A token that the lexer reads back as itself, for the target `T`, when a space or a line break follows
its text. An identifier is a name that is not a reserved word, and a keyword is a reserved word. -/
def TokenKind.ok (T : Edition) : TokenKind → Bool
  | .ident n => identName n && !Lex.reservedWords.contains n
  | .keyword n => Lex.reservedWords.contains n
  | .punct p => Lex.punctuators.contains p
  | .string _ => true
  | .number t => numberOK T (.number t)
  | .bigint t => numberOK T (.bigint t)
  | .eof => false

/-- A word that the lexer reads back as its tokens, for the target `T`: a `lineBreak`, one token that
`TokenKind.ok` accepts, or a `>` that touches the rest of the word. The lexer reads a `>` alone, whatever
follows it, so `>=`, `>>`, `>>>`, `>>=` and `>>>=` are such words. -/
def Word.ok (T : Edition) : Word → Bool
  | [] => true
  | [k] => k.ok T
  | k :: w => k == .punct ">" && Word.ok T w

/-- Each `lineBreak` in the words `ws` comes right before the word `(`. The printer puts a line break
only between `async` and the `(` of a call of it. `Laid` allows a line break inside a line only before a
`(`, so the lexer would not read a line break before any other word as `Laid` states. -/
def breaksOK : List Word → Bool
  | [] => true
  | [] :: ws => ws.head? == some [.punct "("] && breaksOK ws
  | _ :: ws => breaksOK ws

namespace Lex

variable {α β : Type}

/-! ### The lexer's monad -/

theorem bind_ok {x : LexM α} {f : α → LexM β} {s s' : LexState} {b : β} :
    (x >>= f) s = .ok b s' ↔ ∃ a s₁, x s = .ok a s₁ ∧ f a s₁ = .ok b s' := by
  simp only [bind, EStateM.bind]
  cases h : x s with
  | ok a s₁ =>
    simp only [EStateM.Result.ok.injEq]
    constructor
    · intro h'; exact ⟨a, s₁, ⟨rfl, rfl⟩, h'⟩
    · rintro ⟨a', s₂, ⟨rfl, rfl⟩, h'⟩; exact h'
  | error e s₁ => simp

theorem bind_eq {x : LexM α} {f : α → LexM β} {s s₁ : LexState} {a : α} (h : x s = .ok a s₁) :
    (x >>= f) s = f a s₁ := by
  simp only [bind, EStateM.bind, h]

/-- The value and the state after a run that succeeds, and `none` after one that fails. A proof can then
state what a function of the lexer gives as a function on `Option`, and step through a `bind` with
`okOf_bind`. -/
def okOf : EStateM.Result ParseError LexState α → Option (α × LexState)
  | .ok a s => some (a, s)
  | .error _ _ => none

@[simp] theorem okOf_ok (a : α) (s : LexState) :
    okOf (.ok a s : EStateM.Result ParseError LexState α) = some (a, s) := rfl

theorem okOf_bind (x : LexM α) (f : α → LexM β) (s : LexState) :
    okOf ((x >>= f) s) = (okOf (x s)).bind fun p => okOf (f p.1 p.2) := by
  simp only [bind, EStateM.bind]
  cases x s <;> rfl

theorem okOf_eq_some {r : EStateM.Result ParseError LexState α} {a : α} {s : LexState} :
    okOf r = some (a, s) ↔ r = .ok a s := by
  cases r <;> simp [okOf]

@[simp] theorem okOf_pure (a : α) (s : LexState) : okOf ((pure a : LexM α) s) = some (a, s) := rfl

@[simp] theorem okOf_map (f : α → β) (x : LexM α) (s : LexState) :
    okOf ((f <$> x) s) = (okOf (x s)).map fun p => (f p.1, p.2) := by
  show okOf ((x >>= fun a => pure (f a)) s) = _
  rw [okOf_bind]; cases okOf (x s) <;> rfl

@[simp] theorem okOf_ite {c : Prop} [Decidable c] (x y : LexM α) (s : LexState) :
    okOf ((if c then x else y) s) = if c then okOf (x s) else okOf (y s) := by
  split <;> rfl

/-- The state after `skipChar` runs `n` times: `n` characters on, on the same line. -/
def skipped (s : LexState) (n : Nat) : LexState :=
  { s with rest := s.rest.drop n, i := s.i + n, col := s.col + n }

@[simp] theorem skipped_zero (s : LexState) : skipped s 0 = s := by simp [skipped]

@[simp] theorem skipped_skipped (s : LexState) (m n : Nat) :
    skipped (skipped s m) n = skipped s (m + n) := by
  simp only [skipped, List.drop_drop]; congr 1 <;> omega

@[simp] theorem skipped_rest (s : LexState) (n : Nat) : (skipped s n).rest = s.rest.drop n := rfl
@[simp] theorem skipped_i (s : LexState) (n : Nat) : (skipped s n).i = s.i + n := rfl
@[simp] theorem skipped_target (s : LexState) (n : Nat) : (skipped s n).target = s.target := rfl
@[simp] theorem skipped_size (s : LexState) (n : Nat) : (skipped s n).size = s.size := rfl
@[simp] theorem skipped_tokens (s : LexState) (n : Nat) : (skipped s n).tokens = s.tokens := rfl
@[simp] theorem skipped_newline (s : LexState) (n : Nat) : (skipped s n).newline = s.newline := rfl

theorem skipChar_eq (s : LexState) : skipChar s = .ok () (skipped s 1) := rfl
theorem peekChar_eq (k : Nat) (s : LexState) : peekChar k s = .ok s.rest[k]? s := rfl
theorem get_eq (s : LexState) : (get : LexM LexState) s = .ok s s := rfl
theorem budget_eq (s : LexState) : budget s = .ok (s.size - s.i + 1) s := rfl
theorem here_eq (s : LexState) : here s = .ok ⟨s.line, s.col⟩ s := rfl
@[simp] theorem okOf_failFrom (start : Pos) (m : String) (s : LexState) :
    okOf (failFrom (A := α) start m s) = none := rfl
@[simp] theorem okOf_skipChar (s : LexState) : okOf (skipChar s) = some ((), skipped s 1) := rfl
@[simp] theorem okOf_peekChar (k : Nat) (s : LexState) : okOf (peekChar k s) = some (s.rest[k]?, s) := rfl
@[simp] theorem okOf_get (s : LexState) : okOf ((get : LexM LexState) s) = some (s, s) := rfl
@[simp] theorem okOf_budget (s : LexState) : okOf (budget s) = some (s.size - s.i + 1, s) := rfl

/-! ### What every function of the lexer keeps -/

/-- The characters left fit in the size, so `budget` gives every loop enough fuel. -/
def Fits (s : LexState) : Prop := s.rest.length ≤ s.size - s.i

/-- A run from `s` to `s'` keeps the tokens, the size and the target. If the characters left fit in the
size before the run, they also fit after it. -/
structure Kept (s s' : LexState) : Prop where
  tokens : s'.tokens = s.tokens
  size : s'.size = s.size
  target : s'.target = s.target
  fits : Fits s → Fits s'

theorem Kept.refl (s : LexState) : Kept s s := ⟨rfl, rfl, rfl, id⟩

theorem Kept.trans {s₁ s₂ s₃ : LexState} (h₁ : Kept s₁ s₂) (h₂ : Kept s₂ s₃) : Kept s₁ s₃ :=
  ⟨h₂.tokens.trans h₁.tokens, h₂.size.trans h₁.size, h₂.target.trans h₁.target, h₂.fits ∘ h₁.fits⟩

/-- Every run of `p` that succeeds keeps what `Kept` states. -/
structure Keeps (p : LexM α) : Prop where
  kept : ∀ s a s', p s = .ok a s' → Kept s s'

theorem keeps_pure (a : α) : Keeps (pure a : LexM α) := by
  constructor; intro s b s' h
  simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h
  obtain ⟨_, rfl⟩ := h
  exact Kept.refl _

theorem keeps_bind {x : LexM α} {f : α → LexM β} (hx : Keeps x) (hf : ∀ a, Keeps (f a)) :
    Keeps (x >>= f) := by
  constructor; intro s b s' h
  obtain ⟨a, s₁, h₁, h₂⟩ := bind_ok.mp h
  exact (hx.kept _ _ _ h₁).trans ((hf a).kept _ _ _ h₂)

theorem keeps_ite {c : Prop} [Decidable c] {x y : LexM α} (hx : Keeps x) (hy : Keeps y) :
    Keeps (if c then x else y) := by
  split <;> assumption

theorem keeps_get : Keeps (get : LexM LexState) := by
  constructor; intro s a s' h
  simp only [get, getThe, MonadStateOf.get, EStateM.get, EStateM.Result.ok.injEq] at h
  obtain ⟨_, rfl⟩ := h
  exact Kept.refl _

theorem keeps_throw (e : ParseError) : Keeps (throw e : LexM α) := by
  constructor; intro s a s' h
  simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

theorem keeps_skipChar : Keeps skipChar := by
  constructor; intro s a s' h
  simp only [skipChar, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    EStateM.Result.ok.injEq] at h
  obtain ⟨_, rfl⟩ := h
  refine ⟨rfl, rfl, rfl, fun hf => ?_⟩
  simp only [Fits, List.length_drop] at hf ⊢
  omega

theorem keeps_skipLineBreak : Keeps skipLineBreak := by
  constructor; intro s a s' h
  simp only [skipLineBreak, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    EStateM.Result.ok.injEq] at h
  obtain ⟨_, rfl⟩ := h
  refine ⟨rfl, rfl, rfl, fun hf => ?_⟩
  simp only [Fits, List.length_drop] at hf ⊢
  split <;> omega

theorem keeps_peekChar (k : Nat) : Keeps (peekChar k) := keeps_bind keeps_get fun _ => keeps_pure _
theorem keeps_here : Keeps here := keeps_bind keeps_get fun _ => keeps_pure _
theorem keeps_budget : Keeps budget := keeps_bind keeps_get fun _ => keeps_pure _
theorem keeps_failFrom (start : Pos) (m : String) : Keeps (failFrom (A := α) start m) :=
  keeps_bind keeps_here fun _ => keeps_throw _
theorem keeps_outOfFuel : Keeps (outOfFuel (A := α)) := keeps_bind keeps_here fun _ => keeps_failFrom _ _
theorem keeps_takeAs (acc : String) (c : Char) : Keeps (takeAs acc c) :=
  keeps_bind keeps_skipChar fun _ => keeps_pure _

/-- One step of the tactic `keeps`. Each `macro_rules` for it adds a lemma that the step may apply. -/
syntax "keeps_one" : tactic
macro_rules | `(tactic| keeps_one) => `(tactic| first
  | intro _ | apply keeps_pure | apply keeps_get | apply keeps_throw | apply keeps_skipChar
  | apply keeps_skipLineBreak | apply keeps_peekChar | apply keeps_here | apply keeps_budget
  | apply keeps_failFrom | apply keeps_outOfFuel | apply keeps_takeAs | apply keeps_bind | apply keeps_ite
  | split | assumption | apply_assumption | contradiction)

/-- Proves `Keeps p` by stepping through the code of `p`. -/
macro "keeps" : tactic => `(tactic| repeat' keeps_one)

theorem keeps_skipLineComment (f : Nat) : Keeps (skipLineComment f) := by
  induction f with
  | zero => rw [skipLineComment]; keeps
  | succ f ih => rw [skipLineComment]; keeps

theorem keeps_skipBlockComment (f : Nat) (start : Pos) : Keeps (skipBlockComment f start) := by
  induction f with
  | zero => rw [skipBlockComment]; keeps
  | succ f ih => rw [skipBlockComment]; keeps

macro_rules | `(tactic| keeps_one) => `(tactic| apply keeps_skipLineComment)
macro_rules | `(tactic| keeps_one) => `(tactic| apply keeps_skipBlockComment)

theorem keeps_skipTrivia (f : Nat) : Keeps (skipTrivia f) := by
  induction f with
  | zero => rw [skipTrivia]; keeps
  | succ f ih => rw [skipTrivia]; keeps

theorem keeps_readHex (start : Pos) (count acc : Nat) : Keeps (readHex start count acc) := by
  induction count generalizing acc with
  | zero => rw [readHex]; keeps
  | succ n ih => rw [readHex]; keeps

theorem keeps_readBracedHex (f : Nat) (start : Pos) (digits acc : Nat) :
    Keeps (readBracedHex f start digits acc) := by
  induction f generalizing digits acc with
  | zero => rw [readBracedHex]; keeps
  | succ n ih => rw [readBracedHex]; keeps

macro_rules | `(tactic| keeps_one) => `(tactic| apply keeps_readHex)
macro_rules | `(tactic| keeps_one) => `(tactic| apply keeps_readBracedHex)

theorem keeps_readCodeUnit (start : Pos) : Keeps (readCodeUnit start) := by
  unfold readCodeUnit; keeps

macro_rules | `(tactic| keeps_one) => `(tactic| apply keeps_readCodeUnit)

theorem keeps_readCodePoint (start : Pos) : Keeps (readCodePoint start) := by
  unfold readCodePoint; keeps

macro_rules | `(tactic| keeps_one) => `(tactic| apply keeps_readCodePoint)

theorem keeps_readEscape (start : Pos) (acc : String) : Keeps (readEscape start acc) := by
  unfold readEscape; keeps

macro_rules | `(tactic| keeps_one) => `(tactic| apply keeps_readEscape)

theorem keeps_readStringBody (f : Nat) (start : Pos) (q : Char) (acc : String) :
    Keeps (readStringBody f start q acc) := by
  induction f generalizing acc with
  | zero => rw [readStringBody]; keeps
  | succ n ih => rw [readStringBody]; keeps

/-! ### Digits -/

/-- How many characters `readMoreDigits` reads from `cs`, or `none` where it fails. -/
def moreDigits (d : Char → Bool) : List Char → Option Nat
  | [] => some 0
  | c :: cs =>
    if d c then (moreDigits d cs).map (· + 1)
    else if c == '_' then (if cs.head?.any d then (moreDigits d cs).map (· + 1) else none)
    else some 0

/-- How many characters `readDigits` reads from `cs`. -/
def digitsOf (d : Char → Bool) : List Char → Option Nat
  | c :: cs => if d c then (moreDigits d cs).map (· + 1) else none
  | [] => none

/-- With enough fuel, `readMoreDigits` reads what `moreDigits` states. -/
theorem readMoreDigits_eq (f : Nat) (start : Pos) (d : Char → Bool) (s : LexState) (h : s.rest.length < f) :
    okOf (readMoreDigits f start d s) = (moreDigits d s.rest).map fun j => ((), skipped s j) := by
  induction f generalizing s with
  | zero => omega
  | succ f ih =>
    rw [readMoreDigits]
    simp only [okOf_bind, okOf_peekChar, Option.bind_some]
    match hr : s.rest with
    | [] => simp [moreDigits]
    | c :: cs =>
      have hl : (skipped s 1).rest.length < f := by simp [hr] at h ⊢; omega
      have hih := ih (skipped s 1) hl
      simp only [skipped_rest, hr, List.drop_succ_cons, List.drop_zero] at hih
      by_cases hd : d c
      · simp [moreDigits, hd, okOf_bind, hih, Option.map_map, Function.comp_def, Nat.add_comm]
      · by_cases hu : c = '_'
        · subst hu
          by_cases hn : cs[0]?.any d
          · simp [moreDigits, hd, hn, okOf_bind, hih, Option.map_map, Function.comp_def, Nat.add_comm, hr,
              List.head?_eq_getElem?]
          · simp [moreDigits, hd, hn, hr, okOf_bind, List.head?_eq_getElem?]
        · simp [moreDigits, hd, hu]

theorem readDigits_eq (start : Pos) (d : Char → Bool) (s : LexState) (h : Fits s) :
    okOf (readDigits start d s) = (digitsOf d s.rest).map fun j => ((), skipped s j) := by
  unfold readDigits
  simp only [okOf_bind, okOf_peekChar, Option.bind_some]
  match hr : s.rest with
  | [] => simp [digitsOf]
  | c :: cs =>
    by_cases hd : d c
    · have hl : (skipped s 1).rest.length < (skipped s 1).size - (skipped s 1).i + 1 := by
        simp only [Fits, hr, List.length_cons] at h
        simp only [skipped_rest, skipped_size, skipped_i, hr, List.length_drop, List.length_cons]; omega
      simp only [List.getElem?_cons_zero, hd, if_true, okOf_bind, okOf_skipChar, Option.bind_some, okOf_budget]
      rw [readMoreDigits_eq _ _ _ _ hl]
      simp [digitsOf, hd, hr, Option.map_map, Function.comp_def, Nat.add_comm]
    · simp [digitsOf, hd]

/-! ### `lexNumber` in named steps -/

/-- The end of `lexNumber`: the `n` of a bigint, the checks on what follows, and the token. -/
def numEnd (start : Pos) (i0 : Nat) (rest0 : List Char) (isInteger : Bool) : LexM TokenKind := do
  let isBigint := (← peekChar) == some 'n'
  if isBigint then
    if !isInteger then failFrom start "a bigint literal must be an integer"
    skipChar
  if (← peekChar).any (fun c => isIdentStart c || c.isDigit) then
    failFrom start "an identifier or a digit cannot follow a number directly"
  let s ← get
  let chars := rest0.take (s.i - i0)
  let text := charsToString chars
  if isBigint && !s.target.supports .bigint then
    failFrom start (Feature.bigint.refusal s.target)
  if chars.contains '_' && !s.target.supports .numericSeparators then
    failFrom start (Feature.numericSeparators.refusal s.target)
  return if isBigint then .bigint text else .number text

/-- The exponent of a decimal number. -/
def numExp (start : Pos) (i0 : Nat) (rest0 : List Char) (isInteger : Bool) : LexM TokenKind := do
  if (← peekChar).any (fun c => c == 'e' || c == 'E') then
    skipChar
    if (← peekChar).any (fun c => c == '+' || c == '-') then skipChar
    readDigits start Char.isDigit
    numEnd start i0 rest0 false
  else numEnd start i0 rest0 isInteger

/-- The fraction of a decimal number. -/
def numDot (start : Pos) (i0 : Nat) (rest0 : List Char) (isInteger : Bool) : LexM TokenKind := do
  if (← peekChar) == some '.' then
    skipChar
    if (← peekChar).any Char.isDigit then readDigits start Char.isDigit
    numExp start i0 rest0 false
  else numExp start i0 rest0 isInteger

/-- The radix that the first two characters choose, as `lexNumber` computes it. -/
def radixOf (first second : Option Char) : Option (Char → Bool) :=
  if first != some '0' then none
  else match second with
    | some 'x' | some 'X' => some isHexDigit
    | some 'b' | some 'B' => some fun c => c == '0' || c == '1'
    | some 'o' | some 'O' => some fun c => '0' ≤ c && c ≤ '7'
    | _ => none

/-- `lexNumber`, with its steps as named functions, so that a lemma can state what each step reads.
`lexNumber_steps` shows that it is `lexNumber`. -/
def lexNumberSteps (start : Pos) : LexM TokenKind := do
  let i0 := (← get).i
  let rest0 := (← get).rest
  let first ← peekChar
  let second ← peekChar 1
  match radixOf first second with
  | some isDigit =>
    skipChar
    skipChar
    readDigits start isDigit
    numEnd start i0 rest0 true
  | none =>
    if first == some '0' && second.any (fun c => c.isDigit || c == '_') then
      failFrom start "a number cannot start with 0 unless it is 0 (legacy octal is not supported)"
    if first != some '.' then readDigits start Char.isDigit
    numDot start i0 rest0 true

theorem lexNumber_steps (start : Pos) : lexNumber start = lexNumberSteps start := by
  funext s; rfl

/-! ### `lexNumber` on a list of characters -/

/-- What `numEnd` gives when `lexNumber` starts at the characters `cs` and has read `n` of them: the token
and how many characters it has, or `none` where `numEnd` fails. -/
def endOf (T : Edition) (cs : List Char) (n : Nat) (isInteger : Bool) : Option (TokenKind × Nat) :=
  let isBigint := cs[n]? == some 'n'
  if isBigint && !isInteger then none
  else
    let m := if isBigint then n + 1 else n
    if cs[m]?.any (fun c => isIdentStart c || c.isDigit) then none
    else if isBigint && !T.supports .bigint then none
    else if (cs.take m).contains '_' && !T.supports .numericSeparators then none
    else some (if isBigint then .bigint (charsToString (cs.take m)) else .number (charsToString (cs.take m)), m)

/-- What `numExp` gives, as `endOf` states it for `numEnd`. -/
def expOf (T : Edition) (cs : List Char) (n : Nat) (isInteger : Bool) : Option (TokenKind × Nat) :=
  if cs[n]?.any (fun c => c == 'e' || c == 'E') then
    let n₁ := if cs[n + 1]?.any (fun c => c == '+' || c == '-') then n + 2 else n + 1
    (digitsOf Char.isDigit (cs.drop n₁)).bind fun j => endOf T cs (n₁ + j) false
  else endOf T cs n isInteger

/-- What `numDot` gives, as `endOf` states it for `numEnd`. -/
def dotOf (T : Edition) (cs : List Char) (n : Nat) (isInteger : Bool) : Option (TokenKind × Nat) :=
  if cs[n]? == some '.' then
    (if cs[n + 1]?.any Char.isDigit then (digitsOf Char.isDigit (cs.drop (n + 1))).map (n + 1 + ·)
     else some (n + 1)).bind fun n₂ => expOf T cs n₂ false
  else expOf T cs n isInteger

/-- What `lexNumber` gives when it starts at the characters `cs`: the token and how many characters it
has, or `none` where it fails (`lexNumber_eq`). -/
def numberOf (T : Edition) (cs : List Char) : Option (TokenKind × Nat) :=
  match radixOf cs[0]? cs[1]? with
  | some d => (digitsOf d (cs.drop 2)).bind fun j => endOf T cs (2 + j) true
  | none =>
    if cs[0]? == some '0' && cs[1]?.any (fun c => c.isDigit || c == '_') then none
    else (if cs[0]? != some '.' then digitsOf Char.isDigit cs else some 0).bind fun n => dotOf T cs n true

theorem fits_skipped {s : LexState} (h : Fits s) (n : Nat) : Fits (skipped s n) := by
  simp only [Fits, skipped_rest, skipped_size, skipped_i, List.length_drop] at h ⊢; omega

theorem numEnd_eq (start : Pos) (s : LexState) (n : Nat) (isInteger : Bool) :
    okOf (numEnd start s.i s.rest isInteger (skipped s n)) =
      (endOf s.target s.rest n isInteger).map fun p => (p.1, skipped s p.2) := by
  unfold numEnd endOf
  by_cases hb : s.rest[n]? = some 'n'
  · cases isInteger
    · simp [okOf_bind, hb]
    · simp [okOf_bind, hb, Nat.add_assoc, Nat.add_sub_cancel_left]
      (repeat' split) <;> simp_all
  · simp [okOf_bind, hb, Nat.add_assoc, Nat.add_sub_cancel_left]
    (repeat' split) <;> simp_all

theorem numExp_eq (start : Pos) (s : LexState) (h : Fits s) (n : Nat) (isInteger : Bool) :
    okOf (numExp start s.i s.rest isInteger (skipped s n)) =
      (expOf s.target s.rest n isInteger).map fun p => (p.1, skipped s p.2) := by
  have hd := fun n => readDigits_eq start Char.isDigit (skipped s n) (fits_skipped h n)
  have he := fun n b => numEnd_eq start s n b
  simp only [skipped_rest, skipped_skipped] at hd
  unfold numExp expOf
  simp only [okOf_bind, okOf_peekChar, Option.bind_some, skipped_rest, List.getElem?_drop, Nat.add_zero]
  split
  · simp only [okOf_bind, okOf_skipChar, Option.bind_some, skipped_skipped, okOf_peekChar, skipped_rest,
      List.getElem?_drop, Nat.add_zero]
    split
    · simp only [okOf_bind, okOf_skipChar, Option.bind_some, skipped_skipped, hd, Option.bind_map,
        Function.comp_def, he, Option.map_bind]
    · simp only [okOf_bind, okOf_pure, Option.bind_some, hd, Option.bind_map, Function.comp_def, he,
        Option.map_bind]
  · exact he n isInteger

theorem numDot_eq (start : Pos) (s : LexState) (h : Fits s) (n : Nat) (isInteger : Bool) :
    okOf (numDot start s.i s.rest isInteger (skipped s n)) =
      (dotOf s.target s.rest n isInteger).map fun p => (p.1, skipped s p.2) := by
  have hd := fun n => readDigits_eq start Char.isDigit (skipped s n) (fits_skipped h n)
  have he := fun n b => numExp_eq start s h n b
  simp only [skipped_rest, skipped_skipped] at hd
  unfold numDot dotOf
  simp only [okOf_bind, okOf_peekChar, Option.bind_some, skipped_rest, List.getElem?_drop, Nat.add_zero]
  split
  · simp only [okOf_bind, okOf_skipChar, Option.bind_some, skipped_skipped, okOf_peekChar, skipped_rest,
      List.getElem?_drop, Nat.add_zero]
    split
    · simp only [okOf_bind, hd, Option.bind_map, Function.comp_def, he, Option.map_bind, Option.map_map]
    · simp only [okOf_bind, okOf_pure, Option.bind_some, he]
  · exact he n isInteger

/-- `lexNumber` reads what `numberOf` states. -/
theorem lexNumber_eq (start : Pos) (s : LexState) (h : Fits s) :
    okOf (lexNumber start s) = (numberOf s.target s.rest).map fun p => (p.1, skipped s p.2) := by
  have hd := fun d n => readDigits_eq start d (skipped s n) (fits_skipped h n)
  have hn := fun n b => numEnd_eq start s n b
  have hD := fun n b => numDot_eq start s h n b
  have hd0 := readDigits_eq start Char.isDigit s h
  have hD0 : ∀ b, okOf (numDot start s.i s.rest b s) =
      (dotOf s.target s.rest 0 b).map fun p => (p.1, skipped s p.2) := fun b => by simpa using hD 0 b
  simp only [skipped_rest, skipped_skipped] at hd
  rw [lexNumber_steps]
  unfold lexNumberSteps numberOf
  simp only [okOf_bind, okOf_get, okOf_peekChar, Option.bind_some]
  cases hr : radixOf s.rest[0]? s.rest[1]? with
  | some d =>
    simp only [okOf_bind, okOf_skipChar, Option.bind_some, skipped_skipped, hd, Option.bind_map,
      Function.comp_def, hn, Option.map_bind]
  | none =>
    simp only [hr]
    split
    · simp [okOf_bind]
    · simp only [okOf_bind, okOf_pure, Option.bind_some]
      split
      · simp only [okOf_bind, hd0, Option.bind_map, Function.comp_def, hD, Option.map_bind]
      · simp only [okOf_bind, okOf_pure, Option.bind_some, hD0]

/-! ### How far a number reads -/

theorem moreDigits_le {d : Char → Bool} :
    ∀ {cs : List Char} {j : Nat}, moreDigits d cs = some j → j ≤ cs.length
  | [], j, h => by simp [moreDigits] at h; omega
  | c :: cs, j, h => by
    simp only [moreDigits] at h
    split at h
    · obtain ⟨j', h', rfl⟩ := Option.map_eq_some_iff.mp h
      have := moreDigits_le h'; simp; omega
    · split at h
      · split at h
        · obtain ⟨j', h', rfl⟩ := Option.map_eq_some_iff.mp h
          have := moreDigits_le h'; simp; omega
        · simp at h
      · simp at h; omega

theorem digitsOf_le {d : Char → Bool} {cs : List Char} {j : Nat} (h : digitsOf d cs = some j) :
    1 ≤ j ∧ j ≤ cs.length := by
  match cs, h with
  | c :: cs, h =>
    simp only [digitsOf] at h
    split at h
    · obtain ⟨j', h', rfl⟩ := Option.map_eq_some_iff.mp h
      have := moreDigits_le h'; simp; omega
    · simp at h

/-- What the end of a number gives: the token, and where it stops. -/
theorem endOf_some {T : Edition} {cs : List Char} {n : Nat} {b : Bool} {k : TokenKind} {m : Nat}
    (h : endOf T cs n b = some (k, m)) :
    n ≤ m ∧ (n < m → m ≤ cs.length) ∧ cs[m]?.any (fun c => isIdentStart c || c.isDigit) = false ∧
      (k = .number (charsToString (cs.take m)) ∨ k = .bigint (charsToString (cs.take m))) := by
  unfold endOf at h
  by_cases hb : cs[n]? = some 'n'
  · have hn : n < cs.length := (List.getElem?_eq_some_iff.mp hb).1
    simp only [hb, beq_self_eq_true, Bool.true_and] at h
    split at h
    · simp at h
    · simp only [if_true] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨by omega, fun _ => by omega, Bool.eq_false_iff.mpr ‹_›, Or.inr rfl⟩
  · have hb' : (cs[n]? == some 'n') = false := by simpa using hb
    simp only [hb', Bool.false_and, Bool.false_eq_true, if_false] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by omega, fun h => by omega, Bool.eq_false_iff.mpr ‹_›, Or.inl rfl⟩

/-- A number ends in `numEnd`, at or after the position where `numExp` starts. -/
theorem expOf_some {T : Edition} {cs : List Char} {n : Nat} {b : Bool} {k : TokenKind} {m : Nat}
    (h : expOf T cs n b = some (k, m)) :
    ∃ n' b', endOf T cs n' b' = some (k, m) ∧ n ≤ n' ∧ (n < n' → n' ≤ cs.length) := by
  unfold expOf at h
  split at h
  · simp only at h
    obtain ⟨j, hj, he⟩ := Option.bind_eq_some_iff.mp h
    have := digitsOf_le hj
    simp only [List.length_drop] at this
    refine ⟨_, _, he, by split <;> omega, fun _ => by split <;> split at this <;> omega⟩
  · exact ⟨n, b, h, Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩

/-- A number ends in `numEnd`, at or after the position where `numDot` starts. -/
theorem dotOf_some {T : Edition} {cs : List Char} {n : Nat} {b : Bool} {k : TokenKind} {m : Nat}
    (h : dotOf T cs n b = some (k, m)) :
    ∃ n' b', endOf T cs n' b' = some (k, m) ∧ n ≤ n' ∧ (n < n' → n' ≤ cs.length) := by
  unfold dotOf at h
  split at h
  · rename_i hd
    have hn : n < cs.length := by
      simp only [beq_iff_eq] at hd; exact (List.getElem?_eq_some_iff.mp hd).1
    obtain ⟨n₂, h₂, he⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨n', b', he', h₁, h₃⟩ := expOf_some he
    have : n + 1 ≤ n₂ ∧ n₂ ≤ cs.length := by
      split at h₂
      · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h₂
        have := digitsOf_le hj; simp only [List.length_drop] at this; omega
      · simp only [Option.some.injEq] at h₂; omega
    exact ⟨n', b', he', by omega, fun _ => by omega⟩
  · exact expOf_some h

/-- A number ends in `numEnd`, after at least one character. -/
theorem numberOf_some {T : Edition} {cs : List Char} {k : TokenKind} {m : Nat} (h : numberOf T cs = some (k, m)) :
    ∃ n' b', endOf T cs n' b' = some (k, m) ∧ 0 < n' ∧ n' ≤ cs.length := by
  unfold numberOf at h
  split at h
  · obtain ⟨j, hj, he⟩ := Option.bind_eq_some_iff.mp h
    have := digitsOf_le hj; simp only [List.length_drop] at this
    exact ⟨_, _, he, by omega, by omega⟩
  · split at h
    · simp at h
    · obtain ⟨n, hn, he⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨n', b', he', h₁, h₂⟩ := dotOf_some he
      split at hn
      · have := digitsOf_le hn
        exact ⟨n', b', he', by omega, by omega⟩
      · rename_i hd
        simp only [Option.some.injEq] at hn; subst hn
        have hd' : cs[0]? = some '.' := by simpa using hd
        have h0 : 0 < cs.length := (List.getElem?_eq_some_iff.mp hd').1
        unfold dotOf at he
        rw [if_pos (by simp [hd'])] at he
        obtain ⟨n₂, h₃, he₂⟩ := Option.bind_eq_some_iff.mp he
        obtain ⟨n'', b'', he'', h₄, h₅⟩ := expOf_some he₂
        have : 1 ≤ n₂ ∧ n₂ ≤ cs.length := by
          split at h₃
          · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h₃
            have := digitsOf_le hj; simp only [List.length_drop] at this; omega
          · simp only [Option.some.injEq] at h₃; omega
        exact ⟨n'', b'', he'', by omega, by omega⟩

/-- A number that the lexer gives has at least one character, and no digit or letter follows it. Its
token is its text. -/
theorem numberOf_ok {T : Edition} {cs : List Char} {k : TokenKind} {m : Nat} (h : numberOf T cs = some (k, m)) :
    0 < m ∧ m ≤ cs.length ∧ cs[m]?.any (fun c => isIdentStart c || c.isDigit) = false ∧
      (k = .number (charsToString (cs.take m)) ∨ k = .bigint (charsToString (cs.take m))) := by
  obtain ⟨n', b', he, h₁, h₂⟩ := numberOf_some h
  obtain ⟨h₃, h₄, h₅, h₆⟩ := endOf_some he
  exact ⟨by omega, by omega, h₅, h₆⟩

/-! ### What follows a number -/

/-- What follows a number in a second source, `r₂`, stops the lexer where `r₁` stops it in the first: `r₂`
starts with the same character as `r₁`, or with a space or a line break, or is empty. The lexer tests the
character after a number for a digit, `_`, `.`, `e`, `n` and the like, and a space or a line break is none
of them. -/
def StopsAlike (r₁ r₂ : List Char) : Prop := r₂.head? = r₁.head? ∨ ∀ c ∈ r₂.head?, c = ' ' ∨ c = '\n'

theorem StopsAlike.look {r₁ r₂ : List Char} (hi : StopsAlike r₁ r₂) {f : Option Char → Bool}
    (hf : f none = false ∧ f (some ' ') = false ∧ f (some '\n') = false) (h : f r₁.head? = false) :
    f r₂.head? = false := by
  rcases hi with hi | hi
  · rw [hi, h]
  · cases r₂ with
    | nil => exact hf.1
    | cons c _ =>
      rcases hi c rfl with rfl | rfl
      · exact hf.2.1
      · exact hf.2.2

theorem look_lt {t r : List Char} {j : Nat} (h : j < t.length) : (t ++ r)[j]? = t[j]? :=
  List.getElem?_append_left h

theorem look_len (t r : List Char) : (t ++ r)[t.length]? = r.head? := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.head?_eq_getElem?]

/-- A test at `j` reads the same in both sources: inside `t` they agree, and at its end the first test
fails, so the second does as well. -/
theorem look_eq {t r₁ r₂ : List Char} (hi : StopsAlike r₁ r₂) {j : Nat} (hj : j ≤ t.length)
    {f : Option Char → Bool}
    (hf : f none = false ∧ f (some ' ') = false ∧ f (some '\n') = false)
    (h : j = t.length → f (t ++ r₁)[j]? = false) : f (t ++ r₂)[j]? = f (t ++ r₁)[j]? := by
  rcases Nat.lt_or_eq_of_le hj with hj | rfl
  · rw [look_lt hj, look_lt hj]
  · have h1 := h rfl
    rw [look_len] at h1
    rw [look_len, look_len, h1]
    exact hi.look hf h1

theorem moreDigits_pos {d : Char → Bool} {cs : List Char} {j : Nat} (hd : cs.head?.any d = true)
    (h : moreDigits d cs = some j) : 1 ≤ j := by
  match cs, hd with
  | c :: cs, hd =>
    simp only [List.head?_cons, Option.any_some] at hd
    simp only [moreDigits, hd, if_true] at h
    obtain ⟨j', _, rfl⟩ := Option.map_eq_some_iff.mp h
    omega

/-- Digits that stop inside `u`, or at its end, stop at the same place in both sources. -/
theorem moreDigits_frame {d : Char → Bool} (hd : d ' ' = false ∧ d '\n' = false) {r₁ r₂ : List Char}
    (hi : StopsAlike r₁ r₂) :
    ∀ {u : List Char} {j : Nat}, moreDigits d (u ++ r₁) = some j → j ≤ u.length →
      moreDigits d (u ++ r₂) = some j
  | [], j, h, hj => by
    simp only [List.length_nil, Nat.le_zero] at hj; subst hj
    simp only [List.nil_append] at h ⊢
    -- The first source stops at its start, so its first character is no digit and no `_`.
    have hs : ∀ r : List Char, moreDigits d r = some 0 ↔ (r.head?.any fun c => d c || c == '_') = false := by
      intro r
      cases r with
      | nil => simp [moreDigits]
      | cons c r =>
        simp only [moreDigits, List.head?_cons, Option.any_some]
        by_cases h1 : d c
        · simp [h1]
        · by_cases h2 : c = '_'
          · subst h2; simp only [h1]; split <;> simp
          · simp [h1, h2]
    rw [hs] at h ⊢
    exact hi.look (f := fun o => o.any fun c => d c || c == '_') (by simp [hd]) h
  | c :: u, j, h, hj => by
    simp only [List.cons_append, moreDigits] at h ⊢
    simp only [List.length_cons] at hj
    split at h
    · rename_i hc
      rw [if_pos hc]
      obtain ⟨j', h', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [moreDigits_frame hd hi h' (by omega)]; rfl
    · rename_i hc
      rw [if_neg hc]
      split at h
      · rename_i hu
        rw [if_pos hu]
        split at h
        · rename_i hn
          obtain ⟨j', h', rfl⟩ := Option.map_eq_some_iff.mp h
          have hn' : ((u ++ r₂).head?.any d) = true := by
            cases u with
            | cons _ _ => simpa using hn
            | nil => simp at hj h' hn; exact absurd (moreDigits_pos (by simpa using hn) h') (by omega)
          rw [if_pos hn', moreDigits_frame hd hi h' (by omega)]; rfl
        · simp at h
      · rename_i hu
        rw [if_neg hu]; exact h

theorem digitsOf_frame {d : Char → Bool} (hd : d ' ' = false ∧ d '\n' = false) {r₁ r₂ : List Char}
    (hi : StopsAlike r₁ r₂) {u : List Char} {j : Nat} (h : digitsOf d (u ++ r₁) = some j)
    (hj : j ≤ u.length) : digitsOf d (u ++ r₂) = some j := by
  cases u with
  | nil => have := digitsOf_le h; simp at hj; omega
  | cons c u =>
    simp only [List.cons_append, digitsOf] at h ⊢
    split at h
    · rename_i hc
      rw [if_pos hc]
      obtain ⟨j', h', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [moreDigits_frame hd hi h' (by simp at hj; omega)]; rfl
    · simp at h

/-- The end of a number that stops at the end of `t` reads the same in both sources. -/
theorem endOf_frame {T : Edition} {t r₁ r₂ : List Char} (hi : StopsAlike r₁ r₂) {n : Nat} {b : Bool}
    {k : TokenKind} (h : endOf T (t ++ r₁) n b = some (k, t.length)) :
    endOf T (t ++ r₂) n b = some (k, t.length) := by
  have hstop := (endOf_some h).2.2.1
  rw [look_len] at hstop
  have hstop₂ := hi.look (f := fun o => o.any fun c => isIdentStart c || c.isDigit) (by decide) hstop
  unfold endOf at h ⊢
  by_cases hb : (t ++ r₁)[n]? = some 'n'
  · simp only [hb, beq_self_eq_true, Bool.true_and, if_true] at h
    split at h
    · simp at h
    · have hn : n + 1 = t.length := by
        split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2
      have hb₂ : (t ++ r₂)[n]? = some 'n' := by rw [look_lt (by omega)]; rwa [look_lt (by omega)] at hb
      simp only [hb₂, beq_self_eq_true, Bool.true_and, if_true]
      rw [if_neg ‹_›]
      simp only [hn, look_len, List.take_left'] at h ⊢
      simp only [hstop, hstop₂, Bool.false_eq_true, if_false] at h ⊢; exact h
  · have hb' : ((t ++ r₁)[n]? == some 'n') = false := by simpa using hb
    simp only [hb', Bool.false_and, Bool.false_eq_true, if_false] at h
    have hn : n = t.length := by
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2
    subst hn
    have hb₂ : ((t ++ r₂)[t.length]? == some 'n') = false := by
      rw [look_len] at hb' ⊢
      exact hi.look (f := fun o => o == some 'n') (by decide) hb'
    simp only [hb₂, Bool.false_and, Bool.false_eq_true, if_false]
    simp only [look_len, List.take_left'] at h ⊢
    simp only [hstop, hstop₂, Bool.false_eq_true, if_false] at h ⊢; exact h

theorem endOf_le {T : Edition} {cs : List Char} {n : Nat} {b : Bool} {k : TokenKind} {m : Nat}
    (h : endOf T cs n b = some (k, m)) : n ≤ m := (endOf_some h).1

theorem expOf_le {T : Edition} {cs : List Char} {n : Nat} {b : Bool} {k : TokenKind} {m : Nat}
    (h : expOf T cs n b = some (k, m)) : n ≤ m := by
  obtain ⟨_, _, he, h₁, _⟩ := expOf_some h
  have := endOf_le he; omega

theorem expOf_frame {T : Edition} {t r₁ r₂ : List Char} (hi : StopsAlike r₁ r₂) {n : Nat} {b : Bool}
    {k : TokenKind} (h : expOf T (t ++ r₁) n b = some (k, t.length)) (hn : n ≤ t.length) :
    expOf T (t ++ r₂) n b = some (k, t.length) := by
  unfold expOf at h ⊢
  by_cases he : (t ++ r₁)[n]?.any (fun c => c == 'e' || c == 'E') = true
  · rw [if_pos he] at h
    simp only at h ⊢
    have key : n + 1 < t.length := by
      obtain ⟨j, hj, hk⟩ := Option.bind_eq_some_iff.mp h
      have := digitsOf_le hj; have := endOf_le hk
      split at this <;> omega
    rw [look_lt (by omega)] at he
    rw [look_lt (by omega), if_pos he]
    rw [look_lt key] at h; rw [look_lt key]
    obtain ⟨j, hj, hk⟩ := Option.bind_eq_some_iff.mp h
    have hj' := digitsOf_le hj
    have hk' := endOf_le hk
    have hn₁ : (if t[n + 1]?.any (fun c => c == '+' || c == '-') = true then n + 2 else n + 1) ≤ t.length := by
      split <;> split at hk' <;> omega
    rw [List.drop_append_of_le_length hn₁] at hj
    rw [List.drop_append_of_le_length hn₁,
      digitsOf_frame (by decide) hi hj (by simp only [List.length_drop]; omega)]
    exact endOf_frame hi hk
  · rw [if_neg he] at h
    have he₂ := look_eq hi hn (f := fun o => o.any fun c => c == 'e' || c == 'E') (by decide)
      (fun _ => by simpa using he)
    rw [if_neg (by simp only at he₂; rw [he₂]; exact he)]
    exact endOf_frame hi h

theorem dotOf_frame {T : Edition} {t r₁ r₂ : List Char} (hi : StopsAlike r₁ r₂) {n : Nat} {b : Bool}
    {k : TokenKind} (h : dotOf T (t ++ r₁) n b = some (k, t.length)) (hn : n ≤ t.length) :
    dotOf T (t ++ r₂) n b = some (k, t.length) := by
  unfold dotOf at h ⊢
  by_cases hdot : ((t ++ r₁)[n]? == some '.') = true
  · rw [if_pos hdot] at h
    obtain ⟨n₂, h₂, he⟩ := Option.bind_eq_some_iff.mp h
    have hle := expOf_le he
    have hn₂ : n + 1 ≤ n₂ := by
      split at h₂
      · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h₂; omega
      · simp only [Option.some.injEq] at h₂; omega
    rw [look_lt (by omega)] at hdot
    rw [look_lt (by omega), if_pos hdot]
    by_cases hdig : (t ++ r₁)[n + 1]?.any Char.isDigit = true
    · rw [if_pos hdig] at h₂
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h₂
      have := digitsOf_le hj
      rw [look_lt (by omega)] at hdig
      rw [look_lt (by omega), if_pos hdig]
      rw [List.drop_append_of_le_length (by omega)] at hj
      rw [List.drop_append_of_le_length (by omega),
        digitsOf_frame (by decide) hi hj (by simp only [List.length_drop]; omega)]
      exact expOf_frame hi he (by omega)
    · rw [if_neg hdig] at h₂
      simp only [Option.some.injEq] at h₂; subst h₂
      have hdig₂ := look_eq hi (by omega) (f := fun o => o.any Char.isDigit) (by decide)
        (fun _ => by simpa using hdig)
      rw [if_neg (by simp only at hdig₂; rw [hdig₂]; exact hdig)]
      exact expOf_frame hi he (by omega)
  · rw [if_neg hdot] at h
    have hdot₂ := look_eq hi hn (f := fun o => o == some '.') (by decide) (fun _ => by simpa using hdot)
    rw [if_neg (by simp only at hdot₂; rw [hdot₂]; exact hdot)]
    exact expOf_frame hi h hn

theorem dotOf_le {T : Edition} {cs : List Char} {n : Nat} {b : Bool} {k : TokenKind} {m : Nat}
    (h : dotOf T cs n b = some (k, m)) : n ≤ m := by
  obtain ⟨_, _, he, h₁, _⟩ := dotOf_some h
  have := endOf_le he; omega

theorem radixOf_none (a : Option Char) : radixOf a none = none ∧ radixOf a (some ' ') = none ∧
    radixOf a (some '\n') = none := by
  unfold radixOf; split <;> simp

theorem radixOf_blank {a b : Option Char} {d : Char → Bool} (h : radixOf a b = some d) :
    d ' ' = false ∧ d '\n' = false := by
  unfold radixOf at h
  split at h
  · simp at h
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> decide

/-- A number reads the same in a second source when what follows it there stops the lexer as well. So the
lexer reads a number that it gives in a source again when a space follows it, and the other way round. -/
theorem numberOf_frame {T : Edition} {t r₁ r₂ : List Char} (hi : StopsAlike r₁ r₂) {k : TokenKind}
    (h : numberOf T (t ++ r₁) = some (k, t.length)) :
    numberOf T (t ++ r₂) = some (k, t.length) := by
  have hpos := (numberOf_ok h).1
  unfold numberOf at h ⊢
  rw [look_lt hpos] at h; rw [look_lt hpos]
  cases hr : radixOf t[0]? (t ++ r₁)[1]? with
  | some d =>
    simp only [hr] at h
    obtain ⟨j, hj, he⟩ := Option.bind_eq_some_iff.mp h
    have := digitsOf_le hj; have := endOf_le he
    simp only [List.length_drop] at this
    rw [look_lt (by omega)] at hr; rw [look_lt (by omega), hr]
    simp only
    rw [List.drop_append_of_le_length (by omega)] at hj
    rw [List.drop_append_of_le_length (by omega),
      digitsOf_frame (radixOf_blank hr) hi hj (by simp only [List.length_drop]; omega)]
    exact endOf_frame hi he
  | none =>
    simp only [hr] at h
    have hr₂ := look_eq hi (j := 1) hpos (f := fun o => (radixOf t[0]? o).isSome)
      (by simp [radixOf_none]) (fun _ => by simp [hr])
    have hr₂' : radixOf t[0]? (t ++ r₂)[1]? = none := by simpa [hr] using hr₂
    rw [hr₂']; simp only
    split at h
    · simp at h
    · rename_i hz
      have hz₂ := look_eq hi (j := 1) hpos
        (f := fun o => t[0]? == some '0' && o.any (fun c => c.isDigit || c == '_')) (by simp)
        (fun _ => by simpa using hz)
      rw [if_neg (by simp only at hz₂; rw [hz₂]; exact hz)]
      obtain ⟨n, hn, he⟩ := Option.bind_eq_some_iff.mp h
      have hle := dotOf_le he
      have hd := (numberOf_ok (T := T) (cs := t ++ r₁) (k := k) (m := t.length) (by
        unfold numberOf; rw [look_lt hpos]; simp only [hr]; rw [if_neg hz]; exact h)).2.1
      split at hn
      · rename_i hdot
        rw [if_pos hdot]
        have := digitsOf_le hn
        rw [digitsOf_frame (u := t) (by decide) hi hn (by omega)]
        exact dotOf_frame hi he hle
      · rename_i hdot
        rw [if_neg hdot]
        simp only [Option.some.injEq] at hn; subst hn
        exact dotOf_frame hi he (Nat.zero_le _)

/-! ### Names -/

theorem foldl_push_toList (cs : List Char) (acc : String) :
    (cs.foldl String.push acc).toList = acc.toList ++ cs := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih => simp [List.foldl, ih, String.toList_push]

theorem charsToString_toList (cs : List Char) : (charsToString cs).toList = cs := by
  simp [charsToString, foldl_push_toList]

/-- With enough fuel, `readWhile` reads the characters at the front that pass `p`. -/
theorem readWhile_eq (f : Nat) (p : Char → Bool) (acc : String) (s : LexState) (h : s.rest.length < f) :
    readWhile f p acc s =
      .ok ((s.rest.takeWhile p).foldl String.push acc) (skipped s (s.rest.takeWhile p).length) := by
  induction f generalizing acc s with
  | zero => omega
  | succ f ih =>
    rw [readWhile]
    apply okOf_eq_some.mp
    simp only [okOf_bind, okOf_peekChar, Option.bind_some]
    match hr : s.rest with
    | [] => simp
    | c :: cs =>
      by_cases hp : p c
      · have hl : (skipped s 1).rest.length < f := by simp [hr] at h ⊢; omega
        have := ih (acc.push c) (skipped s 1) hl
        simp only [skipped_rest, hr, List.drop_succ_cons, List.drop_zero, skipped_skipped] at this
        simp [hp, takeAs, okOf_bind, this, List.takeWhile_cons, Nat.add_comm]
      · simp [hp, List.takeWhile_cons]

/-! ### Punctuators -/

theorem forIn_range_skip (k n : Nat) (s : LexState) :
    (forIn (List.range' k n 1) PUnit.unit fun _ _ => do skipChar; pure (ForInStep.yield PUnit.unit) :
      LexM PUnit) s = .ok () (skipped s n) := by
  induction n generalizing k s with
  | zero => simp [List.range']; rfl
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    rw [bind_eq (by rw [bind_eq (skipChar_eq s)]; rfl)]
    simp only
    rw [ih]; simp [Nat.add_comm]

/-- The loop at the end of `lexPunct` skips `n` characters. -/
theorem forIn_skip (n : Nat) (s : LexState) :
    (forIn [:n] PUnit.unit fun _ _ => do skipChar; pure (ForInStep.yield PUnit.unit) : LexM PUnit) s =
      .ok () (skipped s n) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [Std.Legacy.Range.size] using forIn_range_skip 0 n s

theorem find?_congr {γ : Type} {f g : γ → Bool} :
    ∀ {l : List γ}, (∀ x ∈ l, f x = g x) → l.find? f = l.find? g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.find?]
    rw [h x (by simp), find?_congr (fun y hy => h y (by simp [hy]))]

theorem startsWith_blank {b : Char} (more : List Char) :
    ∀ (p : List Char) {q : List Char}, b ∉ q → startsWith (p ++ b :: more) q = startsWith p q
  | [], [], _ => rfl
  | [], c :: q, hq => by
    have : b ≠ c := fun h => hq (h ▸ List.mem_cons_self)
    simp [startsWith, this]
  | _ :: _, [], _ => rfl
  | x :: p, c :: q, hq => by
    simp only [List.cons_append, startsWith]
    rw [startsWith_blank more p (fun h => hq (List.mem_cons_of_mem _ h))]

/-- `punctuators` lists the longest first, so a punctuator is the first that it starts with. -/
theorem punctuators_first :
    ∀ p ∈ punctuators, punctuators.find? (fun q => startsWith p.toList q.toList) = some p := by
  decide

theorem punctuators_blank : ∀ q ∈ punctuators, ' ' ∉ q.toList ∧ '\n' ∉ q.toList := by decide

theorem lexPunct_find {p : String} (hp : p ∈ punctuators) {b : Char} (hb : b = ' ' ∨ b = '\n')
    (more : List Char) : punctuators.find? (fun q => startsWith (p.toList ++ b :: more) q.toList) = some p := by
  rw [find?_congr (g := fun q => startsWith p.toList q.toList), punctuators_first p hp]
  intro q hq
  apply startsWith_blank
  rcases hb with rfl | rfl
  · exact (punctuators_blank q hq).1
  · exact (punctuators_blank q hq).2

/-- `lexPunct` reads a punctuator that a space or a line break follows. -/
theorem lexPunct_eq (start : Pos) {p : String} (hp : p ∈ punctuators) {b : Char} (hb : b = ' ' ∨ b = '\n')
    {more : List Char} {s : LexState} (hs : s.rest = p.toList ++ b :: more) :
    lexPunct start s = .ok (.punct p) (skipped s p.length) := by
  have h2 : p = "?." ∨ p = "--" → s.rest[2]? = some b := by
    rintro (rfl | rfl) <;> simp [hs] <;> rfl
  have h1 : (p == "?." && s.rest[2]?.any Char.isDigit) = false := by
    cases hq : p == "?."
    · rfl
    · rw [h2 (Or.inl (by simpa using hq))]; rcases hb with rfl | rfl <;> rfl
  have h3 : (p == "<" && startsWith (s.rest.drop 1) "!--".toList) = false := by
    cases hq : p == "<"
    · rfl
    · have : p = "<" := by simpa using hq
      subst this
      rw [hs]; rcases hb with rfl | rfl <;> rfl
  have h4 : (p == "--" && s.rest[2]? == some '>') = false := by
    cases hq : p == "--"
    · rfl
    · rw [h2 (Or.inr (by simpa using hq))]; rcases hb with rfl | rfl <;> rfl
  unfold lexPunct
  rw [bind_eq (get_eq s)]
  simp only
  rw [hs, lexPunct_find hp hb more, ← hs]
  simp only [h1, h3, h4, Bool.false_eq_true, if_false]
  apply okOf_eq_some.mp
  simp only [okOf_bind, okOf_pure, Option.bind_some, forIn_skip, okOf_ok]

/-- `lexPunct` reads `>` alone, whatever follows it. -/
theorem lexPunct_gt (start : Pos) {more : List Char} {s : LexState} (hs : s.rest = '>' :: more) :
    lexPunct start s = .ok (.punct ">") (skipped s 1) := by
  have hf : punctuators.find? (fun q => startsWith ('>' :: more) q.toList) = some ">" := by
    rw [find?_congr (g := fun q => q == ">")]
    · decide
    · intro q hq
      have key : ∀ q ∈ punctuators, (q = ">" ∧ q.toList = ['>']) ∨
          (q.toList.head?.any (· == '>') = false ∧ q.toList ≠ [] ∧ q ≠ ">") := by decide
      rcases key q hq with ⟨rfl, h⟩ | ⟨h, hn, hne⟩
      · rw [h]; simp [startsWith]
      · rw [beq_false_of_ne hne]
        cases hq' : q.toList with
        | nil => exact absurd hq' hn
        | cons c _ =>
          rw [hq'] at h
          have hc : ('>' == c) = false := by
            simp only [List.head?_cons, Option.any_some] at h
            exact beq_false_of_ne (fun e => by subst e; simp at h)
          simp [startsWith, hc]
  unfold lexPunct
  rw [bind_eq (get_eq s)]
  simp only
  rw [hs, hf]
  have e1 : (">" == "?.") = false := by decide
  have e2 : (">" == "<") = false := by decide
  have e3 : (">" == "--") = false := by decide
  simp only [e1, e2, e3, Bool.false_and, Bool.false_eq_true, if_false]
  apply okOf_eq_some.mp
  simp only [okOf_bind, okOf_pure, Option.bind_some, forIn_skip, okOf_ok]
  rfl

/-! ### Strings -/

/-- How `quote` writes one character of a string. -/
def escChar (c : Char) : String :=
  if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n"
  else if c == '\r' then "\\r" else if c.toNat == 0x2028 then "\\u2028"
  else if c.toNat == 0x2029 then "\\u2029" else c.toString

theorem quote_toList (v : String) :
    (quote v).toList = '"' :: (v.toList.flatMap fun c => (escChar c).toList) ++ ['"'] := by
  simp [quote, escChar, String.toList_append, String.toList_join, List.flatMap_map]

theorem length_escChars :
    ∀ cs : List Char, cs.length ≤ (cs.flatMap fun c => (escChar c).toList).length
  | [] => Nat.le_refl _
  | c :: cs => by
    have := length_escChars cs
    have hc : 1 ≤ (escChar c).toList.length := by
      unfold escChar; repeat' split
      all_goals first | decide | simp
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

/-- `readStringBody` reads one character of a string as `quote` writes it. -/
theorem readStringBody_char (f : Nat) (start : Pos) (acc : String) (c : Char) (r : List Char) (s : LexState)
    (hs : s.rest = (escChar c).toList ++ r) :
    readStringBody (f + 1) start '"' acc s =
      readStringBody f start '"' (acc.push c) (skipped s (escChar c).toList.length) := by
  unfold escChar at hs ⊢
  split
  · rename_i h; have : c = '"' := by simpa using h
    subst this; cases s; simp at hs; subst hs; rfl
  · split
    · rename_i _ h; have : c = '\\' := by simpa using h
      subst this; cases s; simp at hs; subst hs; rfl
    · split
      · rename_i _ _ h; have : c = '\n' := by simpa using h
        subst this; cases s; simp at hs; subst hs; rfl
      · split
        · rename_i _ _ _ h; have : c = '\r' := by simpa using h
          subst this; cases s; simp at hs; subst hs; rfl
        · split
          · rename_i _ _ _ _ h
            have hc : c.toNat = 0x2028 := by simpa using h
            have : c = Char.ofNat 0x2028 := (Char.ofNat_toNat c).symm.trans (by rw [hc])
            subst this; cases s; simp at hs; subst hs; rfl
          · split
            · rename_i _ _ _ _ _ h
              have hc : c.toNat = 0x2029 := by simpa using h
              have : c = Char.ofNat 0x2029 := (Char.ofNat_toNat c).symm.trans (by rw [hc])
              subst this; cases s; simp at hs; subst hs; rfl
            · rename_i h1 h2 h3 h4 h5 h6
              rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6] at hs
              simp only [beq_iff_eq] at h1 h2 h3 h4 h5 h6
              simp only [Char.toString, String.toList_singleton] at hs ⊢
              rw [readStringBody]
              rw [bind_eq (show peekChar 0 s = .ok (some c) s by
                show EStateM.Result.ok s.rest[0]? s = _; rw [hs]; rfl)]
              simp only
              rw [if_neg (by simpa using h1), if_neg (by simp [h3, h4]),
                if_neg (by simp [isLineBreak, h3, h4, h5, h6]), if_neg (by simpa using h2)]
              rw [bind_eq (show takeAs acc c s = .ok (acc.push c) (skipped s 1) from rfl)]
              rfl

/-- `readStringBody` reads the characters of a string as `quote` writes them, up to the closing `"`. -/
theorem readStringBody_quote (start : Pos) :
    ∀ (cs : List Char) (f : Nat) (acc : String) (s : LexState) (r : List Char),
      s.rest = (cs.flatMap fun c => (escChar c).toList) ++ '"' :: r → cs.length < f →
      readStringBody f start '"' acc s =
        .ok (cs.foldl String.push acc) (skipped s ((cs.flatMap fun c => (escChar c).toList).length + 1))
  | [], f + 1, acc, s, r, hs, _ => by
    simp only [List.flatMap_nil, List.nil_append] at hs
    cases s; simp at hs; subst hs; rfl
  | c :: cs, f + 1, acc, s, r, hs, hf => by
    simp only [List.flatMap_cons, List.append_assoc] at hs
    rw [readStringBody_char f start acc c _ s hs,
      readStringBody_quote start cs f (acc.push c) _ r (by simp [hs]) (by simp at hf; omega)]
    simp [Nat.add_assoc]

/-- The lexer reads a string as `quote` writes it. -/
theorem lexKind_string (start : Pos) (v : String) {b : Char} {more : List Char} {s : LexState}
    (hs : s.rest = (quote v).toList ++ b :: more) (hf : Fits s) :
    lexKind start '"' s = .ok (.string v) (skipped s (quote v).toList.length) := by
  have hq := quote_toList v
  have hl := length_escChars v.toList
  unfold lexKind
  rw [if_neg (by decide)]
  rw [bind_eq (peekChar_eq 1 s)]
  rw [if_neg (by simp), if_pos (by decide)]
  rw [bind_eq (skipChar_eq s), bind_eq (budget_eq _)]
  have hs' : (skipped s 1).rest = (v.toList.flatMap fun c => (escChar c).toList) ++ '"' :: b :: more := by
    simp [hs, hq]
  have hfuel : v.toList.length < (skipped s 1).size - (skipped s 1).i + 1 := by
    simp only [Fits, hs, hq, List.length_append, List.length_cons] at hf
    simp only [skipped_size, skipped_i]; omega
  rw [bind_eq (readStringBody_quote start v.toList _ "" _ _ hs' hfuel)]
  have hv : (v.toList.foldl String.push "") = v := String.ext (by simp [foldl_push_toList])
  rw [hv, hq]
  simp [Nat.add_comm]
  rfl

/-! ### One token -/

theorem identName_toList {n : String} (h : identName n = true) :
    ∃ c cs, n.toList = c :: cs ∧ isIdentStart c = true ∧ ∀ x ∈ c :: cs, isIdentPart x = true := by
  unfold identName at h
  match hn : n.toList, h with
  | c :: cs, h =>
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨c, cs, rfl, h.1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have := h.1; unfold isIdentStart at this; unfold isIdentPart
      simp only [Bool.or_eq_true] at this ⊢
      rcases this with (h1 | h1) | h1
      · exact Or.inl (Or.inl (by simp [Char.isAlphanum, h1]))
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h1
    · exact h.2 x hx

theorem blank_not_identPart {b : Char} (hb : b = ' ' ∨ b = '\n') : isIdentPart b = false := by
  rcases hb with rfl | rfl <;> decide

/-- The lexer reads a name that a space or a line break follows as a keyword or an identifier. -/
theorem lexKind_name (start : Pos) {n : String} (hn : identName n = true) {b : Char}
    (hb : b = ' ' ∨ b = '\n') {more : List Char} {s : LexState} (hs : s.rest = n.toList ++ b :: more) (hf : Fits s) :
    ∃ c, n.toList.head? = some c ∧ lexKind start c s =
      .ok (if reservedWords.contains n then .keyword n else .ident n) (skipped s n.toList.length) := by
  obtain ⟨c, cs, hcs, hc, hp⟩ := identName_toList hn
  refine ⟨c, by simp [hcs], ?_⟩
  unfold lexKind
  rw [if_pos hc, bind_eq (budget_eq s)]
  have hw : s.rest.takeWhile isIdentPart = n.toList := by
    rw [hs, List.takeWhile_append_of_pos (by rw [hcs]; exact hp)]
    simp [List.takeWhile_cons, blank_not_identPart hb]
  have hfuel : s.rest.length < s.size - s.i + 1 := by unfold Fits at hf; omega
  rw [bind_eq (readWhile_eq _ _ _ _ hfuel), hw]
  have hv : (n.toList.foldl String.push "") = n := String.ext (by simp [foldl_push_toList])
  rw [hv]; rfl

/-- What `lexKind` and `skipTrivia` test the first character of a punctuator for. -/
theorem punct_start : ∀ p ∈ punctuators, ∀ c ∈ p.toList.head?,
    isIdentStart c = false ∧ c.isDigit = false ∧ c ≠ '"' ∧ c ≠ '\'' ∧ c ≠ '`' ∧ c.toNat < 128 ∧
      isSpace c = false ∧ isLineBreak c = false := by decide

/-- What `lexKind` and `skipTrivia` test the second character of a punctuator for. -/
theorem punct_second : ∀ p ∈ punctuators, p.toList ≠ [] ∧ p.toList[1]?.any Char.isDigit = false ∧
    (p.toList.head? = some '/' → p.toList[1]? = none ∨ p.toList[1]? = some '=') := by decide

/-- The lexer reads a punctuator that a space or a line break follows. -/
theorem lexKind_punct (start : Pos) {p : String} (hp : p ∈ punctuators) {b : Char}
    (hb : b = ' ' ∨ b = '\n') {more : List Char} {s : LexState} (hs : s.rest = p.toList ++ b :: more) :
    ∃ c, p.toList.head? = some c ∧ lexKind start c s = .ok (.punct p) (skipped s p.toList.length) := by
  obtain ⟨hne, h1, _⟩ := punct_second p hp
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, p.toList = c :: cs := by
    cases h : p.toList with | nil => exact absurd h hne | cons c cs => exact ⟨c, cs, rfl⟩
  obtain ⟨hi, hd, hq1, hq2, hbt, hlow, _⟩ := punct_start p hp c (by simp [hcs])
  refine ⟨c, by simp [hcs], ?_⟩
  have hsec : s.rest[1]?.any Char.isDigit = false := by
    rw [hs, hcs]
    cases cs with
    | nil => rcases hb with rfl | rfl <;> rfl
    | cons d _ => simpa [hcs] using h1
  unfold lexKind
  rw [if_neg (by simp [hi]), bind_eq (peekChar_eq 1 s), if_neg (by simp [hd, hsec]),
    if_neg (by simp [hq1, hq2]), if_neg (by simpa using hbt), if_neg (by omega)]
  rw [lexPunct_eq start hp hb hs, String.length_toList]

/-- The lexer reads `>` alone, whatever follows it. -/
theorem lexKind_gt (start : Pos) {more : List Char} {s : LexState} (hs : s.rest = '>' :: more) :
    lexKind start '>' s = .ok (.punct ">") (skipped s 1) := by
  unfold lexKind
  rw [if_neg (by decide), bind_eq (peekChar_eq 1 s), if_neg (by simp), if_neg (by decide),
    if_neg (by decide), if_neg (by decide)]
  exact lexPunct_gt start hs

theorem fits_start (T : Edition) (cs : List Char) :
    Fits { rest := cs, size := cs.length, target := T } := by
  simp [Fits]

/-- What `numberOK` states, as `numberOf` states it. -/
theorem numberOK_some {T : Edition} {k : TokenKind} (h : numberOK T k = true) :
    startsNumber (k.text.toList ++ [' ']) = true ∧
      numberOf T (k.text.toList ++ [' ']) = some (k, k.text.toList.length) := by
  unfold numberOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hs, hm⟩ := h
  refine ⟨hs, ?_⟩
  have he := lexNumber_eq ⟨1, 1⟩ _ (fits_start T (k.text.toList ++ [' ']))
  split at hm
  · rename_i k' s₀ hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨hk, hrest⟩ := hm
    subst k'
    rw [hr, okOf_ok] at he
    obtain ⟨⟨k'', m⟩, hn, hp⟩ := Option.map_eq_some_iff.mp he.symm
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hk'', hs₀⟩ := hp
    subst k'' s₀
    have hl := congrArg List.length hrest
    simp only [skipped_rest, List.length_drop, List.length_append, List.length_cons, List.length_nil] at hl
    have : m = k.text.toList.length := by
      have := (numberOf_ok hn).2.1; simp at this; omega
    subst this; exact hn
  · simp at hm

/-- `numberOK` holds when `numberOf` reads the text of the number followed by a space. -/
theorem numberOK_of {T : Edition} {k : TokenKind} (hs : startsNumber (k.text.toList ++ [' ']) = true)
    (h : numberOf T (k.text.toList ++ [' ']) = some (k, k.text.toList.length)) : numberOK T k = true := by
  have he := lexNumber_eq ⟨1, 1⟩ _ (fits_start T (k.text.toList ++ [' ']))
  simp only [h, Option.map_some] at he
  unfold numberOK
  simp only [okOf_eq_some.mp he, hs, Bool.true_and, beq_self_eq_true]
  simp

/-- A character that `P` accepts is not a space, a line break or `/`, when `P` rejects each of them. A
digit, a `.` and the start of a name are such characters. -/
theorem not_trivia {P : Char → Bool}
    (hP : ∀ c ∈ [' ', '\t', Char.ofNat 11, Char.ofNat 12, Char.ofNat 160, Char.ofNat 65279, '\n', '\r',
      Char.ofNat 0x2028, Char.ofNat 0x2029, '/'], P c = false) {c : Char} (hc : P c = true) :
    isSpace c = false ∧ isLineBreak c = false ∧ c ≠ '/' := by
  have of : ∀ n, c.toNat = n → c = Char.ofNat n := fun n h => (Char.ofNat_toNat c).symm.trans (by rw [h])
  refine ⟨?_, ?_, ?_⟩
  · cases h : isSpace c
    · rfl
    · simp only [isSpace, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ((((h | h) | h) | h) | h) | h
      all_goals first
        | (subst h; simp_all)
        | (have := of _ h; subst this; simp_all)
  · cases h : isLineBreak c
    · rfl
    · simp only [isLineBreak, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ((h | h) | h) | h
      all_goals first
        | (subst h; simp_all)
        | (have := of _ h; subst this; simp_all)
  · rintro rfl; simp_all

/-- A digit is one of the ten ASCII digits. -/
theorem digit_mem {c : Char} (h : c.isDigit = true) :
    c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'] := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, UInt32.le_iff_toNat_le] at h
  have h1 : 48 ≤ c.toNat := h.1
  have h2 : c.toNat ≤ 57 := h.2
  have of : ∀ n, c.toNat = n → c = Char.ofNat n := fun n h => (Char.ofNat_toNat c).symm.trans (by rw [h])
  have : c.toNat = 48 ∨ c.toNat = 49 ∨ c.toNat = 50 ∨ c.toNat = 51 ∨ c.toNat = 52 ∨ c.toNat = 53 ∨
    c.toNat = 54 ∨ c.toNat = 55 ∨ c.toNat = 56 ∨ c.toNat = 57 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h <;> (rw [of _ h]; decide)

theorem digit_not_identStart {c : Char} (h : c.isDigit = true) : isIdentStart c = false := by
  have key : ∀ d ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'], isIdentStart d = false := by decide
  exact key c (digit_mem h)

/-- The lexer reads a number that `numberOK` accepts, when a space or a line break follows it. -/
theorem lexKind_number (start : Pos) {T : Edition} {k : TokenKind} (hk : numberOK T k = true) {b : Char}
    (hb : b = ' ' ∨ b = '\n') {more : List Char} {s : LexState} (hs : s.rest = k.text.toList ++ b :: more)
    (hf : Fits s) (hT : s.target = T) :
    ∃ c, k.text.toList.head? = some c ∧ lexKind start c s = .ok k (skipped s k.text.toList.length) := by
  obtain ⟨hst, hn⟩ := numberOK_some hk
  have hn₂ : numberOf T (k.text.toList ++ b :: more) = some (k, k.text.toList.length) :=
    numberOf_frame (r₁ := [' ']) (Or.inr (by intro c hc; simp at hc; subst hc; exact hb)) hn
  have hl := lexNumber_eq start s hf
  rw [hT, hs, hn₂] at hl
  simp only [Option.map_some] at hl
  have hlex := okOf_eq_some.mp hl
  generalize ht : k.text.toList = text at hst hs hlex
  cases text with
  | nil => simp [startsNumber] at hst
  | cons c cs =>
    refine ⟨c, rfl, ?_⟩
    simp only [startsNumber, List.cons_append, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hst
    have hi : isIdentStart c = false := by
      rcases hst with h | ⟨rfl, _⟩
      · exact digit_not_identStart h
      · decide
    have hd : (c.isDigit || c == '.' && s.rest[1]?.any Char.isDigit) = true := by
      rcases hst with h | ⟨rfl, h⟩
      · simp [h]
      · cases cs with
        | nil => rcases hb with rfl | rfl <;> simp at h
        | cons d _ => simpa [hs] using h
    unfold lexKind
    rw [if_neg (by simp [hi]), bind_eq (peekChar_eq 1 s), if_pos hd]
    exact hlex

theorem reserved_identName : ∀ w ∈ reservedWords, identName w = true := by decide

/-- The lexer reads the text of a printable token `k`, followed by a space or a line break, as `k`. -/
theorem lexKind_text (start : Pos) {T : Edition} {k : TokenKind} (hk : k.ok T = true) {b : Char}
    (hb : b = ' ' ∨ b = '\n') {more : List Char} {s : LexState} (hs : s.rest = k.text.toList ++ b :: more)
    (hf : Fits s) (hT : s.target = T) :
    ∃ c, k.text.toList.head? = some c ∧ lexKind start c s = .ok k (skipped s k.text.toList.length) := by
  cases k with
  | ident n =>
    simp only [TokenKind.ok, Bool.and_eq_true, Bool.not_eq_true'] at hk
    obtain ⟨c, hc, h⟩ := lexKind_name start hk.1 hb hs hf
    rw [if_neg (by rw [hk.2]; decide)] at h
    exact ⟨c, hc, h⟩
  | keyword n =>
    simp only [TokenKind.ok] at hk
    obtain ⟨c, hc, h⟩ := lexKind_name start (reserved_identName n (by simpa using hk)) hb hs hf
    rw [if_pos hk] at h
    exact ⟨c, hc, h⟩
  | punct p =>
    simp only [TokenKind.ok] at hk
    exact lexKind_punct start (by simpa using hk) hb hs
  | string v =>
    refine ⟨'"', by simp [TokenKind.text, quote_toList], lexKind_string start v hs hf⟩
  | number t => exact lexKind_number start hk hb hs hf hT
  | bigint t => exact lexKind_number start hk hb hs hf hT
  | eof => simp [TokenKind.ok] at hk

/-- `cs` starts with no space, line break or comment, so `skipTrivia` reads none of it. -/
def NoTrivia (cs : List Char) : Prop :=
  ∀ c ∈ cs.head?, isSpace c = false ∧ isLineBreak c = false ∧
    (c = '/' → cs[1]? ≠ some '/' ∧ cs[1]? ≠ some '*')

/-- The text of a printable token starts with no trivia. -/
theorem noTrivia_text {T : Edition} {k : TokenKind} (hk : k.ok T = true) {b : Char}
    (hb : b = ' ' ∨ b = '\n') (more : List Char) : NoTrivia (k.text.toList ++ b :: more) := by
  have name : ∀ n, identName n = true → NoTrivia (n.toList ++ b :: more) := by
    intro n hn
    obtain ⟨c, cs, hcs, hc, _⟩ := identName_toList hn
    intro x hx
    rw [hcs] at hx; simp at hx; subst hx
    obtain ⟨h1, h2, h3⟩ := not_trivia (P := isIdentStart) (by decide) hc
    exact ⟨h1, h2, fun h => absurd h h3⟩
  cases k with
  | ident n =>
    simp only [TokenKind.ok, Bool.and_eq_true] at hk
    exact name n hk.1
  | keyword n =>
    simp only [TokenKind.ok] at hk
    exact name n (reserved_identName n (by simpa using hk))
  | punct p =>
    simp only [TokenKind.ok] at hk
    have hp : p ∈ punctuators := by simpa using hk
    obtain ⟨hne, _, h3⟩ := punct_second p hp
    intro c hc
    obtain ⟨cs, hcs⟩ : ∃ cs, p.toList = c :: cs := by
      cases h : p.toList with
      | nil => exact absurd h hne
      | cons d cs => simp [TokenKind.text, h] at hc; exact ⟨cs, by rw [hc]⟩
    obtain ⟨_, _, _, _, _, _, h1, h2⟩ := punct_start p hp c (by simp [hcs])
    refine ⟨h1, h2, fun hc' => ?_⟩
    subst hc'
    have := h3 (by simp [hcs])
    simp only [TokenKind.text, hcs, List.cons_append]
    cases cs with
    | nil => rcases hb with rfl | rfl <;> simp
    | cons d _ => simp [hcs] at this; simp [this]
  | string v =>
    intro c hc
    simp [TokenKind.text, quote_toList] at hc; subst hc
    exact ⟨rfl, rfl, fun h => absurd h (by decide)⟩
  | number t | bigint t =>
    obtain ⟨hst, _⟩ := numberOK_some hk
    intro c hc
    cases ht : (TokenKind.text _).toList with
    | nil => rw [ht] at hst; simp [startsNumber] at hst
    | cons d cs =>
      simp [ht] at hc; subst hc
      rw [ht] at hst
      have hd : (d.isDigit || d == '.') = true := by
        simp only [startsNumber, List.cons_append, Bool.or_eq_true, Bool.and_eq_true] at hst
        rcases hst with h | ⟨h, _⟩ <;> simp [h]
      obtain ⟨h1, h2, h3⟩ := not_trivia (P := fun c => c.isDigit || c == '.') (by decide) hd
      exact ⟨h1, h2, fun h => absurd h h3⟩
  | eof => simp [TokenKind.ok] at hk

theorem skipTrivia_stop (f : Nat) (s : LexState) (h : NoTrivia s.rest) :
    skipTrivia (f + 1) s = .ok () s := by
  rw [skipTrivia, bind_eq (peekChar_eq 0 s)]
  match hr : s.rest with
  | [] => rfl
  | c :: r =>
    have hc := h c (by simp [hr])
    simp only [List.getElem?_cons_zero]
    rw [if_neg (by simp [hc.1]), if_neg (by simp [hc.2.1])]
    split
    · rename_i hsl
      have hsl : c = '/' := by simpa using hsl
      have h1 := hc.2.2 hsl
      rw [bind_eq (peekChar_eq 1 s)]
      generalize s.rest[1]? = o at h1 ⊢
      split
      · exact absurd rfl h1.1
      · exact absurd rfl h1.2
      · rfl
    · rfl

/-- `skipTrivia` reads the spaces and line breaks `g`, and stops where no trivia starts. -/
theorem skipTrivia_gap : ∀ (g : List Char) (f : Nat) (s : LexState) (r : List Char),
    (∀ c ∈ g, c = ' ' ∨ c = '\n') → s.rest = g ++ r → NoTrivia r → g.length < f →
    ∃ s', skipTrivia f s = .ok () s' ∧ s'.rest = r ∧ s'.newline = (s.newline || g.contains '\n') ∧
      (g = [] → s' = s)
  | [], f + 1, s, r, _, hs, hn, _ => ⟨s, skipTrivia_stop f s (by simpa [hs] using hn), by simpa using hs,
      by simp, fun _ => rfl⟩
  | c :: g, f + 1, s, r, hg, hs, hn, hf => by
    rcases hg c (by simp) with rfl | rfl
    · obtain ⟨s', h1, h2, h3, _⟩ := skipTrivia_gap g f (skipped s 1) r (fun c hc => hg c (by simp [hc]))
        (by simp [hs]) hn (by simp at hf; omega)
      refine ⟨s', ?_, h2, by simp [h3], fun h => by cases h⟩
      rw [skipTrivia, bind_eq (peekChar_eq 0 s)]
      simp only [hs, List.cons_append, List.getElem?_cons_zero]
      rw [if_pos (by decide), bind_eq (skipChar_eq s)]
      exact h1
    · obtain ⟨s₁, hlb, hr₁, hn₁⟩ :
          ∃ s₁, skipLineBreak s = .ok () s₁ ∧ s₁.rest = g ++ r ∧ s₁.newline = true :=
        ⟨_, rfl, by simp [hs], rfl⟩
      obtain ⟨s', h1, h2, h3, _⟩ := skipTrivia_gap g f s₁ r (fun c hc => hg c (by simp [hc])) hr₁ hn
        (by simp at hf; omega)
      refine ⟨s', ?_, h2, by simp [h3, hn₁], fun h => by cases h⟩
      rw [skipTrivia, bind_eq (peekChar_eq 0 s)]
      simp only [hs, List.cons_append, List.getElem?_cons_zero]
      rw [if_neg (by decide), if_pos (by decide), bind_eq hlb]
      exact h1

theorem modify_eq (f : LexState → LexState) (s : LexState) : (modify f : LexM Unit) s = .ok () (f s) := rfl

theorem blank_length {g r : List Char} {s : LexState} (hs : s.rest = g ++ r) (hf : Fits s) :
    g.length < s.size - s.i + 1 := by
  unfold Fits at hf; rw [hs, List.length_append] at hf; omega

/-- One step of `lexAll`: the blanks `g`, then the text of a token. -/
theorem lexAll_token {T : Edition} {k : TokenKind} {g text r : List Char} {s : LexState}
    (hg : ∀ c ∈ g, c = ' ' ∨ c = '\n') (hs : s.rest = g ++ (text ++ r)) (hn : NoTrivia (text ++ r))
    (hk : ∀ (start : Pos) (s₁ : LexState), s₁.rest = text ++ r → Fits s₁ → s₁.target = T →
      ∃ c, text.head? = some c ∧ lexKind start c s₁ = .ok k (skipped s₁ text.length))
    (hf : Fits s) (hT : s.target = T) :
    ∃ s' y, (∀ f, lexAll (f + 1) s = lexAll f s') ∧ s'.rest = r ∧ s'.tokens = s.tokens.push y ∧ y.kind = k ∧
      y.newlineBefore = (s.newline || g.contains '\n') ∧ s'.newline = false ∧ Fits s' ∧ s'.target = T ∧
      s'.rest.length < s.rest.length ∧ y.span.stop = ⟨s'.line, s'.col⟩ ∧ (g = [] → y.span.start = ⟨s.line, s.col⟩) := by
  obtain ⟨s₁, hskip, hr₁, hnl, hg₀⟩ := skipTrivia_gap g _ s _ hg hs hn (blank_length hs hf)
  have hkept := (keeps_skipTrivia _).kept _ _ _ hskip
  obtain ⟨c, hc, hlex⟩ := hk ⟨s₁.line, s₁.col⟩ s₁ hr₁ (hkept.fits hf) (hkept.target.trans hT)
  have hpeek : s₁.rest[0]? = some c := by
    rw [hr₁]; cases text with
    | nil => simp at hc
    | cons d _ => simpa using hc
  let s₂ := skipped s₁ text.length
  let y : Token := { kind := k, span := ⟨⟨s₁.line, s₁.col⟩, ⟨s₂.line, s₂.col⟩⟩, newlineBefore := s₁.newline }
  refine ⟨{ s₂ with tokens := s₂.tokens.push y, newline := false }, y, fun f => ?_, by simp [s₂, hr₁],
    by simp [s₂, hkept.tokens], rfl, hnl, rfl, ?_, by simp [s₂, hkept.target, hT], ?_, rfl,
    fun h => by simp [y, hg₀ h]⟩
  · rw [lexAll, bind_eq (budget_eq s), bind_eq hskip, bind_eq (here_eq s₁), bind_eq (get_eq s₁),
      bind_eq (peekChar_eq 0 s₁)]
    simp only [hpeek]
    rw [bind_eq hlex, bind_eq (here_eq _), bind_eq (modify_eq _ _)]
  · have := fits_skipped (hkept.fits hf) text.length
    exact this
  · have : 0 < text.length := by cases text with | nil => simp at hc | cons _ _ => simp
    simp only [s₂, skipped_rest, hr₁, hs, List.length_drop, List.length_append]; omega

/-- The last step of `lexAll`: only blanks are left, and the lexer gives the end of the file. -/
theorem lexAll_end {g : List Char} {s : LexState} (hg : ∀ c ∈ g, c = ' ' ∨ c = '\n') (hs : s.rest = g)
    (hf : Fits s) (f : Nat) :
    ∃ s' y, lexAll (f + 1) s = .ok () s' ∧ s'.tokens = s.tokens.push y ∧ y.kind = .eof := by
  obtain ⟨s₁, hskip, hr₁, _, _⟩ := skipTrivia_gap g _ s [] hg (by simp [hs]) (by simp [NoTrivia])
    (blank_length (r := []) (by simp [hs]) hf)
  have hkept := (keeps_skipTrivia _).kept _ _ _ hskip
  let y : Token := { kind := .eof, span := ⟨⟨s₁.line, s₁.col⟩, ⟨s₁.line, s₁.col⟩⟩, newlineBefore := s₁.newline }
  refine ⟨{ s₁ with tokens := s₁.tokens.push y }, y, ?_, ?_, rfl⟩
  · rw [lexAll, bind_eq (budget_eq s), bind_eq hskip, bind_eq (here_eq s₁), bind_eq (get_eq s₁),
      bind_eq (peekChar_eq 0 s₁)]
    rw [show s₁.rest[0]? = none by rw [hr₁]; rfl]
    rfl
  · simp [hkept.tokens]

/-! ### Words and lines -/

theorem word_text (w : Word) : (Word.text w).toList = w.flatMap fun k => k.text.toList := by
  simp [Word.text, String.toList_join, List.flatMap_map]

/-- The lexer reads the text of a word, after the blanks `g` and before a space or a line break, as its
tokens. -/
theorem lexAll_word {T : Edition} : ∀ {w : Word}, Word.ok T w = true → w ≠ [] →
    ∀ {g r : List Char} {b : Char} {s : LexState}, (∀ c ∈ g, c = ' ' ∨ c = '\n') →
      (b = ' ' ∨ b = '\n') → s.rest = g ++ ((w.flatMap fun k => k.text.toList) ++ b :: r) → Fits s →
      s.target = T →
      ∃ s' a, (∀ f, lexAll (f + a.length) s = lexAll f s') ∧ s'.rest = b :: r ∧
        s'.tokens.toList = s.tokens.toList ++ a ∧ a.map (·.kind) = w ∧ Chained a ∧
        (∀ y ∈ a.head?, y.newlineBefore = (s.newline || g.contains '\n')) ∧
        (∀ y ∈ a.tail, y.newlineBefore = false) ∧
        (g = [] → ∀ y ∈ a.head?, y.span.start = ⟨s.line, s.col⟩) ∧
        s'.newline = false ∧ Fits s' ∧ s'.target = T ∧ s'.rest.length + a.length ≤ s.rest.length
  | [k], hw, _, g, r, b, s, hg, hb, hs, hf, hT => by
    simp only [Word.ok] at hw
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hs
    obtain ⟨s', y, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11⟩ := lexAll_token hg hs (noTrivia_text hw hb r)
      (fun start s₁ hs₁ hf₁ hT₁ => lexKind_text start hw hb hs₁ hf₁ hT₁) hf hT
    refine ⟨s', [y], h1, h2, by simp [h3], by simp [h4], trivial, by simp [h5], by simp,
      fun h => by simp [h11 h], h6, h7, h8, by simp only [List.length_singleton]; omega⟩
  | k :: v :: w, hw, _, g, r, b, s, hg, hb, hs, hf, hT => by
    simp only [Word.ok, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨rfl, hw⟩ := hw
    have hgt : (TokenKind.punct ">").text.toList = ['>'] := rfl
    simp only [List.flatMap_cons, hgt, List.append_assoc] at hs
    obtain ⟨s₁, y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := lexAll_token (text := ['>'])
      (r := v.text.toList ++ ((w.flatMap fun k => k.text.toList) ++ b :: r)) hg hs
      (by intro c hc; simp at hc; subst hc; exact ⟨rfl, rfl, fun h => absurd h (by decide)⟩)
      (fun start s₁ hs₁ _ _ => ⟨'>', rfl, lexKind_gt start hs₁⟩) hf hT
    obtain ⟨s', a, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩ :=
      lexAll_word hw (by simp) (g := []) (r := r) (by simp) hb (by simp [h2, List.flatMap_cons]) h7 h8
    refine ⟨s', y :: a, fun f => by rw [List.length_cons, ← Nat.add_assoc, h1, k1], k2,
      by simp [k3, h3], by simp [h4, k4], ?_, by simp [h5], ?_, fun h => by simp [h11 h], k9, k10, k11, ?_⟩
    · cases a with
      | nil => trivial
      | cons z a =>
        refine ⟨?_, k5⟩
        rw [k8 rfl z rfl, h10]
    · intro z hz
      simp only [List.tail_cons] at hz
      cases a with
      | nil => simp at hz
      | cons x a =>
        rcases List.mem_cons.mp hz with rfl | hz
        · rw [k6 z rfl, h6]; rfl
        · exact k7 z hz
    · simp only [List.length_cons]; omega

theorem wordsText_break (ind : String) (ws : List Word) :
    (wordsText ind ([] :: ws)).toList = '\n' :: ind.toList ++ (wordsText ind ws).toList := by
  simp [wordsText, String.toList_append]

theorem wordsText_one (ind : String) {w : Word} (hw : w ≠ []) :
    (wordsText ind [w]).toList = w.flatMap fun k => k.text.toList := by
  cases w with
  | nil => exact absurd rfl hw
  | cons k w => simp [wordsText, word_text]

theorem wordsText_cons_break (ind : String) {w : Word} (hw : w ≠ []) (ws : List Word) :
    (wordsText ind (w :: [] :: ws)).toList =
      (w.flatMap fun k => k.text.toList) ++ (wordsText ind ([] :: ws)).toList := by
  cases w with
  | nil => exact absurd rfl hw
  | cons k w => simp only [wordsText, String.toList_append, word_text]

theorem wordsText_cons (ind : String) {w v : Word} (hw : w ≠ []) (hv : v ≠ []) (ws : List Word) :
    (wordsText ind (w :: v :: ws)).toList =
      (w.flatMap fun k => k.text.toList) ++ ' ' :: (wordsText ind (v :: ws)).toList := by
  cases w with
  | nil => exact absurd rfl hw
  | cons k w =>
    cases v with
    | nil => exact absurd rfl hv
    | cons j v => simp [wordsText, String.toList_append, word_text]

/-- The lexer reads the words of a line, after the blanks `g` and before the line break at its end, as
tokens that `Touching` describes. -/
theorem lexAll_words {T : Edition} (ind : String) (hind : ∀ c ∈ ind.toList, c = ' ') :
    ∀ {ws : List Word}, (∀ w ∈ ws, Word.ok T w = true) → breaksOK ws = true →
    ∀ {g r : List Char} {s : LexState}, (∀ c ∈ g, c = ' ' ∨ c = '\n') →
      s.rest = g ++ ((wordsText ind ws).toList ++ '\n' :: r) → Fits s → s.target = T →
      ∃ s' a g', (∀ f, lexAll (f + a.length) s = lexAll f s') ∧ s'.rest = g' ++ '\n' :: r ∧
        (∀ c ∈ g', c = ' ' ∨ c = '\n') ∧ s'.tokens.toList = s.tokens.toList ++ a ∧ Touching a ws ∧
        (∀ y ∈ a.tail, NoBreak y) ∧
        (∀ y ∈ a.head?, y.newlineBefore = (s.newline || g.contains '\n' || ws.head? == some [])) ∧
        Fits s' ∧ s'.target = T ∧ s'.rest.length + a.length ≤ s.rest.length
  | [], _, _, g, r, s, hg, hs, hf, hT => by
    refine ⟨s, [], g, fun _ => rfl, by simpa [wordsText] using hs, hg, by simp, rfl, by simp, by simp, hf,
      hT, by simp⟩
  | [] :: ws, hw, hb, g, r, s, hg, hs, hf, hT => by
    simp only [breaksOK, Bool.and_eq_true] at hb
    rw [wordsText_break] at hs
    obtain ⟨s', a, g', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      lexAll_words ind hind (fun w hw' => hw w (by simp [hw'])) hb.2 (g := g ++ '\n' :: ind.toList)
        (r := r)
        (by intro c hc; simp at hc; rcases hc with hc | rfl | hc
            · exact hg c hc
            · exact Or.inr rfl
            · exact Or.inl (hind c hc))
        (by simp [hs]) hf hT
    refine ⟨s', a, g', h1, h2, h3, h4, ⟨[], a, rfl, rfl, fun y hy => by rw [h7 y hy]; simp, h5⟩, h6,
      fun y hy => by rw [h7 y hy]; simp, h8, h9, h10⟩
  | [k :: w], hw, _, g, r, s, hg, hs, hf, hT => by
    rw [wordsText_one ind (List.cons_ne_nil _ _)] at hs
    obtain ⟨s', a, k1, k2, k3, k4, k5, k6, k7, _, _, k10, k11, k12⟩ :=
      lexAll_word (hw _ (by simp)) (List.cons_ne_nil _ _) (r := r) hg (Or.inr rfl) hs hf hT
    refine ⟨s', a, [], k1, by simp [k2], by simp, k3, ⟨a, [], by simp, k4, ⟨k5, by simp⟩, rfl⟩,
      fun y hy _ => k7 y hy, fun y hy => by simp [k6 y hy], k10, k11, k12⟩
  | (k :: w) :: [] :: ws, hw, hb, g, r, s, hg, hs, hf, hT => by
    rw [wordsText_cons_break ind (List.cons_ne_nil _ _), wordsText_break] at hs
    obtain ⟨s₁, a₁, k1, k2, k3, k4, k5, k6, k7, _, _, k10, k11, k12⟩ :=
      lexAll_word (hw (k :: w) (by simp)) (List.cons_ne_nil _ _) (b := '\n')
        (r := ind.toList ++ (wordsText ind ws).toList ++ '\n' :: r) hg (Or.inr rfl) (by simp [hs]) hf hT
    obtain ⟨s', a₂, g', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      lexAll_words ind hind (ws := [] :: ws)
        (fun w hw' => hw w (by simp at hw' ⊢; rcases hw' with h | h <;> simp [h])) hb (g := []) (r := r)
        (by simp) (by rw [k2, wordsText_break]; simp) k10 k11
    have hbr : ws.head? = some [.punct "("] := by
      simp only [breaksOK, Bool.and_eq_true] at hb; simpa using hb.1
    refine ⟨s', a₁ ++ a₂, g',
      fun f => by rw [List.length_append, Nat.add_comm a₁.length, ← Nat.add_assoc, k1, h1],
      h2, h3, by simp [h4, k3], ⟨a₁, a₂, rfl, k4, ⟨k5, by simp⟩, h5⟩, ?_, ?_, h8, h9, ?_⟩
    · cases a₁ with
      | nil => simp at k4
      | cons z a₁ =>
        intro y hy
        simp only [List.cons_append, List.tail_cons, List.mem_append] at hy
        rcases hy with hy | hy
        · exact fun _ => k7 y hy
        · cases a₂ with
          | nil => simp at hy
          | cons x a₂ =>
            rcases List.mem_cons.mp hy with rfl | hy
            · intro hne
              have := h5.kinds
              cases ws with
              | nil => simp at hbr
              | cons v ws =>
                simp at hbr; subst hbr
                simp at this; exact absurd this.1 hne
            · exact h6 y hy
    · cases a₁ with
      | nil => simp at k4
      | cons z a₁ =>
        intro y hy
        have hy' : y ∈ (z :: a₁).head? := by simpa using hy
        rw [k6 y hy']; simp
    · simp only [List.length_append, k2] at h10 k12 ⊢; omega
  | (k :: w) :: (j :: v) :: ws, hw, hb, g, r, s, hg, hs, hf, hT => by
    rw [wordsText_cons ind (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)] at hs
    obtain ⟨s₁, a₁, k1, k2, k3, k4, k5, k6, k7, _, k9, k10, k11, k12⟩ :=
      lexAll_word (hw (k :: w) (by simp)) (List.cons_ne_nil _ _) (b := ' ')
        (r := (wordsText ind ((j :: v) :: ws)).toList ++ '\n' :: r) hg (Or.inl rfl) (by simp [hs]) hf hT
    obtain ⟨s', a₂, g', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      lexAll_words ind hind (ws := (j :: v) :: ws)
        (fun w hw' => hw w (by simp at hw' ⊢; rcases hw' with h | h <;> simp [h])) hb (g := [' '])
        (r := r) (by simp) (by rw [k2]; simp) k10 k11
    have hflag : ∀ y ∈ a₂.head?, y.newlineBefore = false := fun y hy => by rw [h7 y hy, k9]; rfl
    refine ⟨s', a₁ ++ a₂, g',
      fun f => by rw [List.length_append, Nat.add_comm a₁.length, ← Nat.add_assoc, k1, h1],
      h2, h3, by simp [h4, k3], ⟨a₁, a₂, rfl, k4, ⟨k5, fun _ _ _ y hy => hflag y hy⟩, h5⟩, ?_, ?_, h8, h9,
      ?_⟩
    · cases a₁ with
      | nil => simp at k4
      | cons z a₁ =>
        intro y hy
        simp only [List.cons_append, List.tail_cons, List.mem_append] at hy
        rcases hy with hy | hy
        · exact fun _ => k7 y hy
        · cases a₂ with
          | nil => simp at hy
          | cons x a₂ =>
            rcases List.mem_cons.mp hy with rfl | hy
            · exact fun _ => hflag y rfl
            · exact h6 y hy
    · cases a₁ with
      | nil => simp at k4
      | cons z a₁ =>
        intro y hy
        have hy' : y ∈ (z :: a₁).head? := by simpa using hy
        rw [k6 y hy']; simp
    · simp only [List.length_append, k2, List.length_cons] at h10 k12 ⊢; omega

theorem pushn_toList (c : Char) : ∀ n, ("".pushn c n).toList = List.replicate n c
  | 0 => rfl
  | n + 1 => by
    show (("".pushn c n).push c).toList = _
    rw [String.toList_push, pushn_toList c n, List.replicate_succ']

theorem render_cons (l : Line) (ls : List Line) :
    (render (l :: ls)).toList = List.replicate (2 * l.1) ' ' ++
      (wordsText ("".pushn ' ' (2 * l.1 + 4)) l.2).toList ++ '\n' :: (render ls).toList := by
  simp [render, Line.text, String.toList_append, String.toList_join, pushn_toList]

/-- The lexer reads the printed lines, after the blanks `g`, as tokens that `Laid` describes. -/
theorem lexAll_lines {T : Edition} :
    ∀ {lines : List Line}, (∀ l ∈ lines, ∀ w ∈ l.2, Word.ok T w = true) → (∀ l ∈ lines, breaksOK l.2 = true) →
    ∀ {g : List Char} {s : LexState}, (∀ c ∈ g, c = ' ' ∨ c = '\n') → s.rest = g ++ (render lines).toList →
      Fits s → s.target = T →
      ∃ s' a g', (∀ f, lexAll (f + a.length) s = lexAll f s') ∧ s'.rest = g' ∧
        (∀ c ∈ g', c = ' ' ∨ c = '\n') ∧ s'.tokens.toList = s.tokens.toList ++ a ∧ Laid a (lines.map Prod.snd) ∧
        ((s.newline || g.contains '\n') = true → ∀ y ∈ a.head?, y.newlineBefore = true) ∧ Fits s' ∧
        s'.rest.length + a.length ≤ s.rest.length
  | [], _, _, g, s, hg, hs, hf, _ =>
    ⟨s, [], g, fun _ => rfl, by simpa [render] using hs, hg, by simp, rfl, by simp, hf, by simp⟩
  | l :: ls, hw, hb, g, s, hg, hs, hf, hT => by
    rw [render_cons] at hs
    have hind : ∀ c ∈ ("".pushn ' ' (2 * l.1 + 4)).toList, c = ' ' := by
      intro c hc; rw [pushn_toList] at hc; exact (List.mem_replicate.mp hc).2
    obtain ⟨s₁, a₁, g₁, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩ :=
      lexAll_words _ hind (fun w hw' => hw l (by simp) w hw') (hb l (by simp))
        (g := g ++ List.replicate (2 * l.1) ' ') (r := (render ls).toList)
        (by intro c hc; simp at hc; rcases hc with hc | ⟨_, rfl⟩
            · exact hg c hc
            · exact Or.inl rfl)
        (by simp [hs]) hf hT
    obtain ⟨s', a₂, g', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      lexAll_lines (lines := ls) (fun l' hl' => hw l' (by simp [hl']))
        (fun l' hl' => hb l' (by simp [hl'])) (g := g₁ ++ ['\n']) (s := s₁)
        (by intro c hc; simp at hc; rcases hc with hc | rfl
            · exact k3 c hc
            · exact Or.inr rfl)
        (by simp [k2]) k8 k9
    refine ⟨s', a₁ ++ a₂, g',
      fun f => by rw [List.length_append, Nat.add_comm a₁.length, ← Nat.add_assoc, k1, h1],
      h2, h3, by simp [h4, k4], ⟨a₁, a₂, rfl, k5, k6, h6 (by simp), h5⟩, ?_, h7, ?_⟩
    · intro hn y hy
      cases a₁ with
      | cons z a₁ =>
        have hy' : y ∈ (z :: a₁).head? := by simpa using hy
        rw [k7 y hy']
        simp only [Bool.or_eq_true] at hn ⊢
        left; rcases hn with hn | hn
        · exact Or.inl hn
        · right; simp at hn ⊢; exact hn
      | nil => exact h6 (by simp) y (by simpa using hy)
    · simp only [List.length_append, k2] at h8 k10 ⊢
      simp only [List.length_append, List.length_cons, List.length_nil] at h8 k10
      omega

/-! ### The tokens that the lexer gives -/

theorem takeWhile_all {p : Char → Bool} :
    ∀ {l : List Char} {x : Char}, x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | c :: l, x, h => by
    simp only [List.takeWhile_cons] at h
    split at h
    · rename_i hc
      rcases List.mem_cons.mp h with rfl | h
      · exact hc
      · exact takeWhile_all h
    · simp at h

theorem kept_skipped {s : LexState} (hf : Fits s) (n : Nat) : Kept s (skipped s n) :=
  ⟨rfl, rfl, rfl, fun _ => fits_skipped hf n⟩

/-- A punctuator that `lexPunct` gives is one of `punctuators`. -/
theorem lexPunct_ok {start : Pos} {s s' : LexState} {k : TokenKind} (hf : Fits s)
    (h : lexPunct start s = .ok k s') : k.ok s.target = true ∧ Kept s s' := by
  have h' := okOf_eq_some.mpr h
  unfold lexPunct at h'
  simp only [okOf_bind, okOf_get, Option.bind_some] at h'
  cases hp : punctuators.find? (fun p => startsWith s.rest p.toList) with
  | none => simp only [hp] at h'; simp at h'
  | some p =>
    simp only [hp] at h'
    have hmem : p ∈ punctuators := List.mem_of_find?_eq_some hp
    simp only [okOf_ite, okOf_bind, okOf_failFrom, Option.bind_none, okOf_pure, Option.bind_some,
      forIn_skip, okOf_ok] at h'
    repeat' (split at h')
    all_goals first
      | (simp at h'; done)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h'
         obtain ⟨rfl, rfl⟩ := h'
         exact ⟨by simpa [TokenKind.ok] using hmem, kept_skipped hf _⟩)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h'
         obtain ⟨rfl, rfl⟩ := h'
         exact ⟨by simp only [TokenKind.ok]; decide, kept_skipped hf _⟩)

/-- Every token that `lexKind` gives is printable. -/
theorem lexKind_ok {start : Pos} {c : Char} {s s' : LexState} {k : TokenKind}
    (hc : s.rest[0]? = some c) (hf : Fits s) (h : lexKind start c s = .ok k s') : k.ok s.target = true ∧ Kept s s' := by
  have hfuel : s.rest.length < s.size - s.i + 1 := by unfold Fits at hf; omega
  obtain ⟨r, hr⟩ : ∃ r, s.rest = c :: r := by
    cases h' : s.rest with
    | nil => rw [h'] at hc; cases hc
    | cons d r => rw [h'] at hc; simp at hc; exact ⟨r, by rw [hc]⟩
  unfold lexKind at h
  split at h
  · rename_i hi
    rw [bind_eq (budget_eq s), bind_eq (readWhile_eq _ _ _ _ hfuel)] at h
    simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, kept_skipped hf _⟩
    split
    · rename_i hres; exact hres
    · rename_i hres
      simp only [TokenKind.ok, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨?_, by simpa using hres⟩
      have hp : isIdentPart c = true := by
        unfold isIdentStart at hi; unfold isIdentPart
        simp only [Bool.or_eq_true] at hi ⊢
        rcases hi with (h1 | h1) | h1
        · exact Or.inl (Or.inl (by simp [Char.isAlphanum, h1]))
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1
      unfold identName
      rw [foldl_push_toList, hr]
      simp only [List.takeWhile_cons, hp, String.toList_empty, List.nil_append, if_true]
      simp only [hi, Bool.true_and, List.all_eq_true]
      intro x hx
      exact takeWhile_all hx
  · rename_i hi
    rw [bind_eq (peekChar_eq 1 s)] at h
    split at h
    · rename_i hd
      have hl := lexNumber_eq start s hf
      rw [h, okOf_ok] at hl
      obtain ⟨⟨k', m⟩, hn, hp⟩ := Option.map_eq_some_iff.mp hl.symm
      simp only [Prod.mk.injEq] at hp
      obtain ⟨hk, hs'⟩ := hp
      subst hk hs'
      refine ⟨?_, kept_skipped hf _⟩
      obtain ⟨hpos, hle, hstop, hkind⟩ := numberOf_ok hn
      have htext : k'.text.toList = s.rest.take m := by
        rcases hkind with rfl | rfl <;> simp [TokenKind.text, charsToString_toList]
      have hlen : k'.text.toList.length = m := by rw [htext, List.length_take]; omega
      have hn' :
          numberOf s.target (k'.text.toList ++ s.rest.drop m) = some (k', k'.text.toList.length) := by
        rw [htext, List.take_append_drop, ← htext, hlen]; exact hn
      have hn₂ := numberOf_frame (r₂ := [' '])
        (Or.inr (by intro c hc; simp at hc; exact Or.inl hc.symm)) hn'
      have hok := numberOK_of (T := s.target) (k := k') ?_ hn₂
      · rcases hkind with rfl | rfl <;> exact hok
      · rw [htext, hr]
        cases m with
        | zero => omega
        | succ m =>
          simp only [List.take_succ_cons, List.cons_append, startsNumber]
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hd ⊢
          rcases hd with hd | ⟨rfl, hd⟩
          · exact Or.inl hd
          · refine Or.inr ⟨rfl, ?_⟩
            rw [hr] at hd hstop
            cases r with
            | nil => simp at hd
            | cons d r =>
              cases m with
              | zero =>
                simp at hd hstop
                exact absurd hd (by rw [hstop.2]; decide)
              | succ m => simpa using hd
    · split at h
      · obtain ⟨_, s₁, h1, h2⟩ := bind_ok.mp h
        obtain ⟨b, s₂, h3, h4⟩ := bind_ok.mp h2
        obtain ⟨v, s₃, h5, h6⟩ := bind_ok.mp h4
        simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h6
        obtain ⟨rfl, rfl⟩ := h6
        exact ⟨rfl, (keeps_skipChar.kept _ _ _ h1).trans
          ((keeps_budget.kept _ _ _ h3).trans ((keeps_readStringBody _ _ _ _).kept _ _ _ h5))⟩
      · split at h
        · exact absurd (okOf_eq_some.mpr h) (by simp)
        · split at h
          · exact absurd (okOf_eq_some.mpr h) (by simp)
          · exact lexPunct_ok hf h

/-- Every run of `lexAll` adds printable tokens and then the end of the file. -/
theorem lexAll_ok : ∀ (f : Nat) (s s' : LexState), lexAll f s = .ok () s' → Fits s →
    ∃ new e, s'.tokens.toList = s.tokens.toList ++ new ++ [e] ∧ e.kind = .eof ∧
      ∀ y ∈ new, y.kind.ok s.target = true
  | 0, s, s', h, _ => absurd (okOf_eq_some.mpr h) (by
      rw [lexAll]; simp [outOfFuel, okOf_bind, okOf_failFrom]; exact fun n hn => Nat.noConfusion hn)
  | f + 1, s, s', h, hf => by
    rw [lexAll, bind_eq (budget_eq s)] at h
    obtain ⟨_, s₁, h1, h2⟩ := bind_ok.mp h
    have k1 := (keeps_skipTrivia _).kept _ _ _ h1
    rw [bind_eq (here_eq s₁), bind_eq (get_eq s₁), bind_eq (peekChar_eq 0 s₁)] at h2
    cases hc : s₁.rest[0]? with
    | none =>
      rw [hc] at h2
      simp only at h2
      rw [modify_eq] at h2
      simp only [EStateM.Result.ok.injEq] at h2
      obtain ⟨_, rfl⟩ := h2
      exact ⟨[],
        { kind := .eof, span := ⟨⟨s₁.line, s₁.col⟩, ⟨s₁.line, s₁.col⟩⟩, newlineBefore := s₁.newline },
        by simp [k1.tokens], rfl, by simp⟩
    | some c =>
      rw [hc] at h2
      simp only at h2
      obtain ⟨k, s₂, h3, h4⟩ := bind_ok.mp h2
      obtain ⟨hk, k2⟩ := lexKind_ok hc (k1.fits hf) h3
      rw [bind_eq (here_eq s₂), bind_eq (modify_eq _ _)] at h4
      obtain ⟨new, e, e1, e2, e3⟩ := lexAll_ok f _ s' h4 (k2.fits (k1.fits hf))
      refine ⟨{ kind := k, span := ⟨⟨s₁.line, s₁.col⟩, ⟨s₂.line, s₂.col⟩⟩, newlineBefore := s₁.newline } ::
        new, e, by simp [e1, k2.tokens, k1.tokens], e2, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [← k1.target]; exact hk
      · have := e3 y hy; simpa [k2.target, k1.target] using this

/-- The lexer gives printable tokens and then the end of the file. -/
theorem lexChars_tokens {T : Edition} {chars : List Char} {toks : Array Token}
    (h : lexChars chars T = .ok toks) :
    ∃ new e, toks.toList = new ++ [e] ∧ e.kind = .eof ∧ ∀ y ∈ new, y.kind.ok T = true := by
  unfold lexChars at h
  simp only [EStateM.run] at h
  split at h
  · rename_i s₁ hr
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨new, e, e1, e2, e3⟩ := lexAll_ok _ _ _ hr (fits_start T chars)
    exact ⟨new, e, by simpa using e1, e2, e3⟩
  · simp at h

end Lex

/-! ### The lexer's part of the round trip -/

/-- The lexer reads the printed lines as tokens that `Laid` describes, followed by the end of the file.
Each word is one that the lexer reads back (`Word.ok`), and each line break inside a line comes right
before a `(` (`breaksOK`), as the printer writes them. -/
theorem lexChars_render (T : Edition) (lines : List Line)
    (h : ∀ l ∈ lines, ∀ w ∈ l.2, Word.ok T w = true) (hb : ∀ l ∈ lines, breaksOK l.2 = true) :
    ∃ ts e, lexChars (render lines).toList T = .ok (ts ++ [e]).toArray ∧ Laid ts (lines.map Prod.snd) ∧
      e.kind = .eof := by
  let chars := (render lines).toList
  let s₀ : LexState := { rest := chars, size := chars.length, target := T }
  obtain ⟨s', a, g', h1, h2, h3, h4, h5, _, h7, h8⟩ :=
    Lex.lexAll_lines h hb (g := []) (s := s₀) (by simp) (by simp [s₀, chars]) (Lex.fits_start T chars) rfl
  obtain ⟨s'', y, k1, k2, k3⟩ := Lex.lexAll_end h3 h2 h7 (chars.length - a.length)
  refine ⟨a, y, ?_, h5, k3⟩
  have hf : chars.length + 1 = (chars.length - a.length + 1) + a.length := by
    have : s₀.rest.length = chars.length := rfl
    omega
  show (match (Lex.lexAll (chars.length + 1)) s₀ with
    | EStateM.Result.ok _ s => Except.ok s.tokens | EStateM.Result.error e _ => Except.error e) = _
  rw [hf, h1, k1]
  simp only [Except.ok.injEq]
  apply Array.toList_inj.mp
  simp [k2, h4, s₀]

/-- Every token that the lexer gives, apart from the end of the file, is a word that `Word.ok` accepts. So
the printer can write it, and the lexer reads it back. -/
theorem lexChars_ok_kinds (T : Edition) (chars : List Char) (toks : Array Token)
    (h : lexChars chars T = .ok toks) :
    ∀ t ∈ toks.toList, t.kind = .eof ∨ Word.ok T [t.kind] = true := by
  obtain ⟨new, e, e1, e2, e3⟩ := Lex.lexChars_tokens h
  intro t ht
  rw [e1] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact Or.inr (by simpa [Word.ok] using e3 t ht)
  · simp at ht; subst ht; exact Or.inl e2

/-- The lexer's tokens end with the end of the file. -/
theorem lexChars_last_eof (T : Edition) (chars : List Char) (toks : Array Token)
    (h : lexChars chars T = .ok toks) :
    ∃ r e, toks.toList = r ++ [e] ∧ e.kind = .eof := by
  obtain ⟨new, e, e1, e2, _⟩ := Lex.lexChars_tokens h
  exact ⟨new, e, e1, e2⟩

end tolean.TypeScript.Syntax
