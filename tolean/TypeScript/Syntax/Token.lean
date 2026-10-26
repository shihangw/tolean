import tolean.Source

/-!
The tokens of the TypeScript lexer.
-/
namespace tolean.TypeScript.Syntax

open tolean

inductive TokenKind where
  | ident (name : String)
  /-- A reserved word. Contextual words (`let`, `interface`, `type`,
  `readonly`, `of`) are identifiers; the parser reads them by position. -/
  | keyword (word : String)
  /-- A number literal, as written in the source. -/
  | number (text : String)
  /-- A bigint literal, as written in the source, with its `n`. -/
  | bigint (text : String)
  /-- A string literal, with its escapes decoded. -/
  | string (value : String)
  /-- A punctuator. The lexer gives each `>` alone, as `tsc` does; the parser
  joins `>` `>` `=` and the like in expressions, so that `Array<Array<T>>`
  closes two type argument lists. -/
  | punct (symbol : String)
  | eof
deriving Repr, BEq, Inhabited

structure Token where
  kind : TokenKind
  span : Span
  /-- A line break comes between this token and the previous one. Automatic
  semicolon insertion depends on it. -/
  newlineBefore : Bool
deriving Repr, Inhabited

/-- How a token reads in an error message. -/
def TokenKind.describe : TokenKind → String
  | .ident name => s!"identifier '{name}'"
  | .keyword word => s!"'{word}'"
  | .number text => s!"number {text}"
  | .bigint text => s!"bigint {text}"
  | .string _ => "a string"
  | .punct symbol => s!"'{symbol}'"
  | .eof => "the end of the file"

def Token.isPunct (t : Token) (symbol : String) : Bool := t.kind == .punct symbol
def Token.isKeyword (t : Token) (word : String) : Bool := t.kind == .keyword word
def Token.isIdent (t : Token) (name : String) : Bool := t.kind == .ident name
def Token.isAnyIdent (t : Token) : Bool := t.kind matches .ident _
def Token.isEof (t : Token) : Bool := t.kind == .eof

end tolean.TypeScript.Syntax
