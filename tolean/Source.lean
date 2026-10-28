/-!
Positions, spans and parse errors. Every language front end uses them.
-/
namespace tolean

/-- A position in the source. Lines and columns start at 1. A column counts
Unicode code points, not bytes or UTF-16 units. -/
structure Pos where
  line : Nat
  col : Nat
deriving Repr, BEq, DecidableEq, Inhabited

/-- From the first character of a node to the position just after its last. -/
structure Span where
  start : Pos
  stop : Pos
deriving Repr, BEq, DecidableEq, Inhabited

def Span.render (s : Span) : String :=
  s!"{s.start.line}:{s.start.col}-{s.stop.line}:{s.stop.col}"

structure ParseError where
  span : Span
  message : String
deriving Repr, DecidableEq, Inhabited

/-- `file:line:col: message`, the form editors and CI logs link. -/
def ParseError.render (e : ParseError) (file : String) : String :=
  s!"{file}:{e.span.start.line}:{e.span.start.col}: {e.message}"

/-- A declaration of a program of several files, such as a function or an
interface: the file that declares it, and its name in that file. -/
structure DeclRef where
  file : String
  name : String
deriving Repr, DecidableEq, Inhabited

/-- Two keys are equal when their files and their names are. `simp` uses this
to decide a lookup by key. -/
@[simp] theorem DeclRef.beq_def (a b : DeclRef) : (a == b) = (a.file == b.file && a.name == b.name) := by
  cases a; cases b
  rw [Bool.eq_iff_iff]
  simp

/-- `n` in base 16, lower case, padded with zeros to `width` digits. -/
def hexDigits (n : Nat) (width : Nat) : String :=
  let digits := (Nat.toDigits 16 n).foldl String.push ""
  "".pushn '0' (width - digits.length) ++ digits

end tolean
