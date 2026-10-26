import tolean.Go.Syntax.Token

/-!
The Go lexer. It reads the source as Unicode code points and gives the tokens
with their spans, as the Go specification describes.

A line break, or the end of the file, after an identifier, a literal,
`break`, `continue`, `fallthrough`, `return`, `++`, `--`, `)`, `]` or `}`
becomes a `;` token. A block comment that holds a line break counts as one.

It refuses non-ASCII identifiers, imaginary literals, hex floats, and carriage
returns inside raw strings, which `go/scanner` removes from the value.
-/
namespace tolean.Go.Syntax

open tolean

structure LexState where
  src : Array Char
  i : Nat := 0
  line : Nat := 1
  col : Nat := 1
  tokens : Array Token := #[]

abbrev LexM := EStateM ParseError LexState

namespace Lex

def keywords : List String :=
  ["break", "case", "chan", "const", "continue", "default", "defer", "else",
   "fallthrough", "for", "func", "go", "goto", "if", "import", "interface", "map",
   "package", "range", "return", "select", "struct", "switch", "type", "var"]

/-- Longest first, so that the first match is the longest. -/
def punctuators : List String :=
  ["<<=", ">>=", "&^=", "...",
   "&&", "||", "<-", "++", "--", "==", "!=", "<=", ">=", ":=", "+=", "-=", "*=", "/=",
   "%=", "&=", "|=", "^=", "<<", ">>", "&^",
   "+", "-", "*", "/", "%", "&", "|", "^", "<", ">", "=", "!", "~",
   "(", ")", "[", "]", "{", "}", ",", ";", ".", ":"]

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentPart (c : Char) : Bool := c.isAlphanum || c == '_'

def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def charsToString (cs : Array Char) : String := cs.foldl String.push ""

def matchesAt (src : Array Char) (i : Nat) : List Char → Bool
  | [] => true
  | c :: cs => src[i]? == some c && matchesAt src (i + 1) cs

def peekChar (k : Nat := 0) : LexM (Option Char) := do
  let s ← get
  return s.src[s.i + k]?

def here : LexM Pos := do
  let s ← get
  return ⟨s.line, s.col⟩

def failFrom {A : Type} (start : Pos) (message : String) : LexM A := do
  let stop ← here
  throw ({ span := ⟨start, stop⟩, message } : ParseError)

def skipChar : LexM Unit :=
  modify fun s => { s with i := s.i + 1, col := s.col + 1 }

def skipNewline : LexM Unit :=
  modify fun s => { s with i := s.i + 1, line := s.line + 1, col := 1 }

/-- The last token asks for a `;` at a line break. -/
def wantsSemi : LexM Bool := do
  match (← get).tokens.back? with
  | none => return false
  | some t =>
    match t.kind with
    | .ident _ | .lit _ _ => return true
    | .keyword w => return ["break", "continue", "fallthrough", "return"].contains w
    | .punct p => return ["++", "--", ")", "]", "}"].contains p
    | _ => return false

def pushToken (kind : TokenKind) (span : Span) : LexM Unit :=
  modify fun s => { s with tokens := s.tokens.push { kind, span } }

/-- Insert a `;` at a line break if the last token asks for one. -/
def lineBreak : LexM Unit := do
  if ← wantsSemi then
    let p ← here
    pushToken .autoSemi ⟨p, p⟩

partial def skipLineComment : LexM Unit := do
  match ← peekChar with
  | some '\n' | none => return
  | some _ =>
    skipChar
    skipLineComment

/-- Returns whether the comment held a line break. -/
partial def skipBlockComment (start : Pos) (sawNewline : Bool) : LexM Bool := do
  match ← peekChar, ← peekChar 1 with
  | some '*', some '/' =>
    skipChar
    skipChar
    return sawNewline
  | some '\n', _ =>
    skipNewline
    skipBlockComment start true
  | some _, _ =>
    skipChar
    skipBlockComment start sawNewline
  | none, _ => failFrom start "unterminated comment"

partial def skipTrivia : LexM Unit := do
  match ← peekChar with
  | none => return
  | some c =>
    if c == ' ' || c == '\t' || c == '\r' then
      skipChar
      skipTrivia
    else if c == '\n' then
      lineBreak
      skipNewline
      skipTrivia
    else if c == '/' then
      match ← peekChar 1 with
      | some '/' =>
        skipChar
        skipChar
        skipLineComment
        skipTrivia
      | some '*' =>
        let start ← here
        skipChar
        skipChar
        let wantsSemiBefore ← wantsSemi
        if ← skipBlockComment start false then
          if wantsSemiBefore then pushToken .autoSemi ⟨start, start⟩
        skipTrivia
      | _ => return
    else return

partial def skipWhile (p : Char → Bool) : LexM Unit := do
  match ← peekChar with
  | some c =>
    if p c then
      skipChar
      skipWhile p
    else return
  | none => return

/-- Digits and `_` separators. Go checks separators in the parser of
`strconv`; Tolean checks only that a digit follows. -/
def skipDigits (isDigit : Char → Bool) : LexM Unit :=
  skipWhile fun c => isDigit c || c == '_'

def lexNumber (start : Pos) : LexM TokenKind := do
  let i0 := (← get).i
  let first ← peekChar
  let second ← peekChar 1
  let mut kind := LitKind.int
  if first == some '0' && (second == some 'x' || second == some 'X') then
    skipChar
    skipChar
    skipDigits isHexDigit
    if (← peekChar).any (fun c => c == '.' || c == 'p' || c == 'P') then
      failFrom start "hexadecimal floating-point literals are not supported"
  else if first == some '0' && (second == some 'b' || second == some 'B') then
    skipChar
    skipChar
    skipDigits fun c => c == '0' || c == '1'
  else if first == some '0' && (second == some 'o' || second == some 'O') then
    skipChar
    skipChar
    skipDigits fun c => '0' ≤ c && c ≤ '7'
  else
    skipDigits Char.isDigit
    if (← peekChar) == some '.' then
      kind := .float
      skipChar
      skipDigits Char.isDigit
    if (← peekChar).any (fun c => c == 'e' || c == 'E') then
      kind := .float
      skipChar
      if (← peekChar).any (fun c => c == '+' || c == '-') then skipChar
      skipDigits Char.isDigit
  if (← peekChar) == some 'i' then failFrom start "imaginary literals are not supported"
  if (← peekChar).any isIdentPart then
    failFrom start "an identifier or a digit cannot follow a number directly"
  let s ← get
  return .lit kind (charsToString (s.src.extract i0 s.i))

/-- An interpreted string or a rune literal, up to and including `quote`. The
token keeps the source text; escapes are not decoded. -/
partial def skipQuoted (start : Pos) (quote : Char) : LexM Unit := do
  match ← peekChar with
  | none | some '\n' => failFrom start "unterminated literal"
  | some c =>
    skipChar
    if c == quote then return
    if c == '\\' then
      match ← peekChar with
      | none | some '\n' => failFrom start "unterminated literal"
      | some _ => skipChar
    skipQuoted start quote

partial def skipRaw (start : Pos) : LexM Unit := do
  match ← peekChar with
  | none => failFrom start "unterminated raw string"
  | some '`' => skipChar
  | some '\n' =>
    skipNewline
    skipRaw start
  | some '\r' => failFrom start "a carriage return in a raw string is not supported"
  | some _ =>
    skipChar
    skipRaw start

def lexPunct (start : Pos) : LexM TokenKind := do
  let s ← get
  match punctuators.find? (fun p => matchesAt s.src s.i p.toList) with
  | none => failFrom start s!"unsupported character '{s.src[s.i]!}'"
  | some p =>
    for _ in [0:p.length] do skipChar
    return .punct p

def lexKind (start : Pos) (c : Char) : LexM TokenKind := do
  if isIdentStart c then
    let i0 := (← get).i
    skipWhile isIdentPart
    let s ← get
    let name := charsToString (s.src.extract i0 s.i)
    return if keywords.contains name then .keyword name else .ident name
  else if c.isDigit || (c == '.' && (← peekChar 1).any Char.isDigit) then lexNumber start
  else if c == '"' || c == '\'' || c == '`' then
    let i0 := (← get).i
    skipChar
    if c == '`' then skipRaw start else skipQuoted start c
    let s ← get
    let raw := charsToString (s.src.extract i0 s.i)
    return .lit (if c == '\'' then .char else .string) raw
  else if c.toNat ≥ 0x80 then
    failFrom start s!"unsupported character U+{(hexDigits c.toNat 4).map Char.toUpper}"
  else lexPunct start

partial def lexAll : LexM Unit := do
  skipTrivia
  let start ← here
  match ← peekChar with
  | none =>
    lineBreak
    pushToken .eof ⟨start, start⟩
  | some c =>
    let kind ← lexKind start c
    pushToken kind ⟨start, ← here⟩
    lexAll

end Lex

/-- The tokens of `source`. The last token is `eof`. -/
def lex (source : String) : Except ParseError (Array Token) :=
  match Lex.lexAll.run { src := source.toList.toArray } with
  | .ok _ s => .ok s.tokens
  | .error e _ => .error e

end tolean.Go.Syntax
