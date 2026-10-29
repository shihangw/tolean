import tolean.TypeScript.Syntax.Source

/-!
How the tokens of printed lines lie: which tokens touch, and where a line
break comes. The proofs about the parser read tokens that `Laid` describes,
and `lexChars_render` in `Syntax/RoundTripLex.lean` shows that the lexer gives
such tokens for the printed source.
-/
namespace tolean.TypeScript.Syntax

-- The derived `==` on token kinds is equality, so that a proof can read the
-- parser's tests such as `isPunct`.
deriving instance ReflBEq, LawfulBEq for TokenKind

/-- No line break comes before `y`, unless `y` is a `(`. Inside a line, the
printer puts a line break only before the `(` of a call of `async`, so that
`tsc` reads a call (`Syntax/Source.lean`). Most proofs read only whether a
line break comes before a token that is not a `(`, so this is all that they
need. Where a proof reads it before a `(`, after `async` or after `return`,
`Touching` states it exactly. -/
abbrev NoBreak (y : Token) : Prop := y.kind ≠ .punct "(" → y.newlineBefore = false

/-- Each token of `ts` after the first starts where the one before it stops. -/
def Chained : List Token → Prop
  | x :: y :: r => y.span.start = x.span.stop ∧ Chained (y :: r)
  | _ => True

/-- How the tokens `a` of the word `w` stand, when the words `ws` and their
tokens `b` follow: the tokens of a word touch, and the next token starts a new
line after a `lineBreak` and after no other word. -/
def Placed : Word → List Word → List Token → List Token → Prop
  | [], _, _, b => ∀ y ∈ b.head?, y.newlineBefore = true
  | _ :: _, ws, a, b => Chained a ∧ ∀ v ∈ ws.head?, v ≠ [] → ∀ y ∈ b.head?, y.newlineBefore = false

/-- `ts` are the tokens of `words`, in order, and the tokens of each word
touch. The lexer gives that for the printed source: a word such as `>=` has no
space in it. A line break comes before the token after a `lineBreak`, and
before no other token after the first. -/
def Touching : List Token → List Word → Prop
  | ts, [] => ts = []
  | ts, w :: ws => ∃ a b, ts = a ++ b ∧ a.map (·.kind) = w ∧ Placed w ws a b ∧ Touching b ws

/-- `ts` are the tokens of the lines of words `ls`, one line after another.
The tokens of each line touch as `Touching` states, which also states the
line break before the `(` of a call of `async`. A line break comes before the
first token of each line after the first, and no other line break comes
inside a line. -/
def Laid : List Token → List (List Word) → Prop
  | ts, [] => ts = []
  | ts, l :: ls => ∃ a b, ts = a ++ b ∧ Touching a l ∧ (∀ y ∈ a.tail, NoBreak y) ∧
      (∀ y ∈ b.head?, y.newlineBefore = true) ∧ Laid b ls

theorem Touching.kinds : ∀ {ts : List Token} {ws : List Word}, Touching ts ws → ts.map (·.kind) = ws.flatten
  | ts, [], h => by simp [Touching] at h; simp [h]
  | ts, w :: ws, h => by
    obtain ⟨a, b, rfl, ha, _, hb⟩ := h
    simp [ha, hb.kinds]

end tolean.TypeScript.Syntax
