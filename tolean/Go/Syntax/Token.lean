import tolean.Source

/-!
The tokens of the Go lexer.
-/
namespace tolean.Go.Syntax

open tolean

/-- The kind of a basic literal, named as `go/token` names it. -/
inductive LitKind where
  | int
  | float
  | char
  | string
deriving Repr, BEq, Inhabited

def LitKind.name : LitKind → String
  | .int => "INT"
  | .float => "FLOAT"
  | .char => "CHAR"
  | .string => "STRING"

inductive TokenKind where
  | ident (name : String)
  | keyword (word : String)
  /-- A literal, as written in the source. -/
  | lit (kind : LitKind) (raw : String)
  | punct (symbol : String)
  /-- A `;` that the lexer inserted at a line break or at the end of the file,
  as the Go specification requires. -/
  | autoSemi
  | eof
deriving Repr, BEq, Inhabited

structure Token where
  kind : TokenKind
  span : Span
deriving Repr, Inhabited

/-- How a token reads in an error message. -/
def TokenKind.describe : TokenKind → String
  | .ident name => s!"identifier '{name}'"
  | .keyword word => s!"'{word}'"
  | .lit _ raw => s!"literal {raw}"
  | .punct symbol => s!"'{symbol}'"
  | .autoSemi => "a line break"
  | .eof => "the end of the file"

def Token.isPunct (t : Token) (symbol : String) : Bool := t.kind == .punct symbol
def Token.isKeyword (t : Token) (word : String) : Bool := t.kind == .keyword word
def Token.isEof (t : Token) : Bool := t.kind == .eof

/-- A `;`, written or inserted. -/
def Token.isSemi (t : Token) : Bool := t.kind == .punct ";" || t.kind == .autoSemi

end tolean.Go.Syntax
