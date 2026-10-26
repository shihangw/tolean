import tolean.TypeScript.Edition
import tolean.TypeScript.Syntax.Token

/-!
The TypeScript lexer. It reads the source as Unicode code points and gives the
tokens with their spans.

It refuses what Tolean does not read the same way as `tsc` and the JavaScript
engine: template literals, non-ASCII identifiers, escapes in identifiers,
legacy octal numbers and escapes, lone surrogates, and the `<!--` and `-->`
comments that CommonJS scripts allow.

Line breaks are `\n`, `\r\n`, `\r`, U+2028 and U+2029, as in JavaScript and in
`tsc`'s line numbers.
-/
namespace tolean.TypeScript.Syntax

open tolean

structure LexState where
  src : Array Char
  /-- Syntax newer than the target is refused. -/
  target : Edition := .default
  i : Nat := 0
  line : Nat := 1
  col : Nat := 1
  /-- A line break comes after the last token. -/
  newline : Bool := false
  tokens : Array Token := #[]

abbrev LexM := EStateM ParseError LexState

namespace Lex

def reservedWords : List String :=
  ["break", "case", "catch", "class", "const", "continue", "debugger", "default",
   "delete", "do", "else", "enum", "export", "extends", "false", "finally", "for",
   "function", "if", "import", "in", "instanceof", "new", "null", "return", "super",
   "switch", "this", "throw", "true", "try", "typeof", "var", "void", "while", "with"]

/-- Longest first, so that the first match is the longest. There is no `>=`,
`>>`, `>>>`, `>>=` or `>>>=`: see `TokenKind.punct`. -/
def punctuators : List String :=
  ["...", "===", "!==", "**=", "<<=", "&&=", "||=", "??=",
   "=>", "==", "!=", "<=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=",
   "**", "<<", "&&", "||", "??", "?.", "++", "--",
   "{", "}", "(", ")", "[", "]", ";", ",", "<", ">", "+", "-", "*", "/", "%",
   "&", "|", "^", "!", "~", "?", ":", "=", "."]

def isLineBreak (c : Char) : Bool :=
  c == '\n' || c == '\r' || c.toNat == 0x2028 || c.toNat == 0x2029

/-- Tab, vertical tab, form feed, space, no-break space and the byte order
mark. Other Unicode spaces are refused. -/
def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c.toNat == 0x0B || c.toNat == 0x0C || c.toNat == 0xA0 ||
    c.toNat == 0xFEFF

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'
def isIdentPart (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

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

/-- Move past one character that is not a line break. -/
def skipChar : LexM Unit :=
  modify fun s => { s with i := s.i + 1, col := s.col + 1 }

/-- Move past a line break. `\r\n` is one line break. -/
def skipLineBreak : LexM Unit :=
  modify fun s =>
    let width := if s.src[s.i]? == some '\r' && s.src[s.i + 1]? == some '\n' then 2 else 1
    { s with i := s.i + width, line := s.line + 1, col := 1, newline := true }

def takeAs (acc : String) (c : Char) : LexM String := do
  skipChar
  return acc.push c

partial def skipLineComment : LexM Unit := do
  match ← peekChar with
  | some c =>
    if isLineBreak c then return
    skipChar
    skipLineComment
  | none => return

partial def skipBlockComment (start : Pos) : LexM Unit := do
  match ← peekChar, ← peekChar 1 with
  | some '*', some '/' =>
    skipChar
    skipChar
  | some c, _ =>
    if isLineBreak c then skipLineBreak else skipChar
    skipBlockComment start
  | none, _ => failFrom start "unterminated comment"

partial def skipTrivia : LexM Unit := do
  match ← peekChar with
  | none => return
  | some c =>
    if isSpace c then
      skipChar
      skipTrivia
    else if isLineBreak c then
      skipLineBreak
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
        skipBlockComment start
        skipTrivia
      | _ => return
    else return

partial def readWhile (p : Char → Bool) (acc : String) : LexM String := do
  match ← peekChar with
  | some c => if p c then readWhile p (← takeAs acc c) else return acc
  | none => return acc

/-- The digits after the first, with `_` separators between two digits. -/
partial def readMoreDigits (start : Pos) (isDigit : Char → Bool) : LexM Unit := do
  match ← peekChar with
  | some c =>
    if isDigit c then
      skipChar
      readMoreDigits start isDigit
    else if c == '_' then
      if (← peekChar 1).any isDigit then
        skipChar
        readMoreDigits start isDigit
      else failFrom start "a numeric separator must stand between two digits"
    else return
  | none => return

/-- At least one digit, then `readMoreDigits`. -/
def readDigits (start : Pos) (isDigit : Char → Bool) : LexM Unit := do
  match ← peekChar with
  | some c =>
    if isDigit c then
      skipChar
      readMoreDigits start isDigit
    else failFrom start "expected a digit"
  | none => failFrom start "expected a digit"

def lexNumber (start : Pos) : LexM TokenKind := do
  let i0 := (← get).i
  let first ← peekChar
  let second ← peekChar 1
  let mut isInteger := true
  let radix? : Option (Char → Bool) :=
    if first != some '0' then none
    else match second with
      | some 'x' | some 'X' => some isHexDigit
      | some 'b' | some 'B' => some fun c => c == '0' || c == '1'
      | some 'o' | some 'O' => some fun c => '0' ≤ c && c ≤ '7'
      | _ => none
  match radix? with
  | some isDigit =>
    skipChar
    skipChar
    readDigits start isDigit
  | none =>
    if first == some '0' && second.any (fun c => c.isDigit || c == '_') then
      failFrom start "a number cannot start with 0 unless it is 0 (legacy octal is not supported)"
    if first != some '.' then readDigits start Char.isDigit
    if (← peekChar) == some '.' then
      isInteger := false
      skipChar
      if (← peekChar).any Char.isDigit then readDigits start Char.isDigit
    if (← peekChar).any (fun c => c == 'e' || c == 'E') then
      isInteger := false
      skipChar
      if (← peekChar).any (fun c => c == '+' || c == '-') then skipChar
      readDigits start Char.isDigit
  let isBigint := (← peekChar) == some 'n'
  if isBigint then
    if !isInteger then failFrom start "a bigint literal must be an integer"
    skipChar
  if (← peekChar).any (fun c => isIdentStart c || c.isDigit) then
    failFrom start "an identifier or a digit cannot follow a number directly"
  let s ← get
  let text := charsToString (s.src.extract i0 s.i)
  if isBigint && !s.target.supports .bigint then
    failFrom start (Feature.bigint.refusal s.target)
  if text.contains '_' && !s.target.supports .numericSeparators then
    failFrom start (Feature.numericSeparators.refusal s.target)
  return if isBigint then .bigint text else .number text

partial def readHex (start : Pos) (count : Nat) (acc : Nat) : LexM Nat := do
  if count == 0 then return acc
  match ← peekChar with
  | some c =>
    if isHexDigit c then
      skipChar
      readHex start (count - 1) (acc * 16 + hexValue c)
    else failFrom start "expected a hex digit in the escape"
  | none => failFrom start "expected a hex digit in the escape"

/-- The hex digits of `\u{…}`, after the `{`. -/
partial def readBracedHex (start : Pos) (digits : Nat) (acc : Nat) : LexM Nat := do
  match ← peekChar with
  | some '}' =>
    if digits == 0 then failFrom start "expected a hex digit in the escape"
    skipChar
    return acc
  | some c =>
    if isHexDigit c then
      let acc := acc * 16 + hexValue c
      if acc > 0x10FFFF then failFrom start "a code point escape must be at most 10FFFF"
      skipChar
      readBracedHex start (digits + 1) acc
    else failFrom start "expected a hex digit or '}' in the escape"
  | none => failFrom start "unterminated escape"

/-- The value of `\uXXXX` or `\u{…}`, after the `u`. -/
def readCodeUnit (start : Pos) : LexM Nat := do
  if (← peekChar) == some '{' then
    skipChar
    readBracedHex start 0 0
  else readHex start 4 0

/-- A `\u` escape, after the `u`, as one code point. A high surrogate must be
followed by a `\u` escape of a low surrogate; the two make one code point. A
lone surrogate is refused: a Lean `String` cannot hold it. -/
def readCodePoint (start : Pos) : LexM Nat := do
  let v ← readCodeUnit start
  if 0xDC00 ≤ v && v ≤ 0xDFFF then failFrom start "a lone surrogate is not supported"
  if 0xD800 ≤ v && v ≤ 0xDBFF then
    if (← peekChar) == some '\\' && (← peekChar 1) == some 'u' then
      skipChar
      skipChar
      let w ← readCodeUnit start
      if 0xDC00 ≤ w && w ≤ 0xDFFF then
        return 0x10000 + (v - 0xD800) * 0x400 + (w - 0xDC00)
    failFrom start "a lone surrogate is not supported"
  return v

/-- One escape, after the backslash. -/
def readEscape (start : Pos) (acc : String) : LexM String := do
  match ← peekChar with
  | none => failFrom start "unterminated string"
  | some c =>
    if isLineBreak c then
      -- A line continuation adds nothing to the value.
      skipLineBreak
      return acc
    match c with
    | 'n' => takeAs acc '\n'
    | 't' => takeAs acc '\t'
    | 'r' => takeAs acc '\r'
    | 'b' => takeAs acc (Char.ofNat 0x08)
    | 'f' => takeAs acc (Char.ofNat 0x0C)
    | 'v' => takeAs acc (Char.ofNat 0x0B)
    | 'x' =>
      skipChar
      return acc.push (Char.ofNat (← readHex start 2 0))
    | 'u' =>
      skipChar
      return acc.push (Char.ofNat (← readCodePoint start))
    | '0' =>
      if (← peekChar 1).any Char.isDigit then
        failFrom start "octal escapes are not supported"
      takeAs acc (Char.ofNat 0)
    | _ =>
      if c.isDigit then failFrom start "octal escapes are not supported"
      takeAs acc c

partial def readStringBody (start : Pos) (quote : Char) (acc : String) : LexM String := do
  match ← peekChar with
  | none => failFrom start "unterminated string"
  | some c =>
    if c == quote then
      skipChar
      return acc
    else if c == '\n' || c == '\r' then failFrom start "unterminated string"
    else if isLineBreak c then
      -- U+2028 and U+2029 may stand in a string, and still start a new line.
      skipLineBreak
      readStringBody start quote (acc.push c)
    else if c == '\\' then
      skipChar
      readStringBody start quote (← readEscape start acc)
    else readStringBody start quote (← takeAs acc c)

def lexPunct (start : Pos) : LexM TokenKind := do
  let s ← get
  match punctuators.find? (fun p => matchesAt s.src s.i p.toList) with
  | none => failFrom start s!"unsupported character '{s.src[s.i]!}'"
  | some p =>
    -- `a?.5:b` is `a ? .5 : b`.
    let p := if p == "?." && (s.src[s.i + 2]?).any Char.isDigit then "?" else p
    if p == "<" && matchesAt s.src (s.i + 1) "!--".toList then
      failFrom start "'<!--' is not supported: CommonJS reads it as a comment"
    if p == "--" && s.src[s.i + 2]? == some '>' then
      failFrom start "'-->' is not supported: CommonJS reads it as a comment"
    for _ in [0:p.length] do skipChar
    return .punct p

def lexKind (start : Pos) (c : Char) : LexM TokenKind := do
  if isIdentStart c then
    let name ← readWhile isIdentPart ""
    return if reservedWords.contains name then .keyword name else .ident name
  else if c.isDigit || (c == '.' && (← peekChar 1).any Char.isDigit) then lexNumber start
  else if c == '"' || c == '\'' then
    skipChar
    return .string (← readStringBody start c "")
  else if c == '`' then failFrom start "template literals are not supported"
  else if c.toNat ≥ 0x80 then
    failFrom start s!"unsupported character U+{(hexDigits c.toNat 4).map Char.toUpper}"
  else lexPunct start

partial def lexAll : LexM Unit := do
  skipTrivia
  let start ← here
  let newlineBefore := (← get).newline
  match ← peekChar with
  | none =>
    modify fun s =>
      { s with tokens := s.tokens.push { kind := .eof, span := ⟨start, start⟩, newlineBefore } }
  | some c =>
    let kind ← lexKind start c
    let stop ← here
    modify fun s =>
      { s with
        tokens := s.tokens.push { kind, span := ⟨start, stop⟩, newlineBefore }
        newline := false }
    lexAll

end Lex

/-- The tokens of `source`, for the edition `target`. The last token is `eof`. -/
def lex (source : String) (target : Edition := .default) : Except ParseError (Array Token) :=
  match Lex.lexAll.run { src := source.toList.toArray, target } with
  | .ok _ s => .ok s.tokens
  | .error e _ => .error e

end tolean.TypeScript.Syntax
