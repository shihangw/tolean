import tolean.TypeScript.Syntax.Parser

/-!
A syntax tree as TypeScript source, for the round trip of step 4 of the
certificates plan: the parser reads the printed source as the same tree.

The printer writes one form for each node, so that the proof of the round
trip follows the tree:

- Every statement and every declaration has a line of its own, and every
  statement ends in `;`. So no `;` is inserted.
- A statement breaks across lines only where the standard needs a line
  break: between the name `async` and the `(` of a call of it. On one line,
  `tsc` can read `async (` as the start of an async arrow function, such as
  `async () : T => …`. ECMA-262 §15.9 lets no line break come between `async`
  and the parameters of an async arrow function, and `tsc` reads none after
  one either. So `async`, then a line break, then `(`, is a call in both. The
  printer puts no line break at any other place inside a statement. So no
  `[no LineTerminator here]` rule of the standard applies.
- The printer builds lines of words, and `render` writes them with one space
  between two words. A word is one token, or the `>` and `=` tokens of a
  `>=` or a `>>`, which the parser reads as tokens that touch. So no two
  words run together. The empty word `lineBreak` stands for a line break.
- A parenthesis stands only where the tree has a `paren` node, as the parser
  keeps them.
- A string is printed in double quotes, with an escape only for `"`, `\`, `\n`,
  `\r`, U+2028 and U+2029, the characters that cannot stand in it as
  themselves.

The parser keeps where each node starts and stops, and the printed source puts
it elsewhere. So the round trip compares the trees with `erase`, which sets
every span to the same value.
-/
namespace tolean.TypeScript.Syntax

open tolean

/-! ### Printing -/

/-- `s` as a string literal in double quotes. -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n"
    else if c == '\r' then "\\r" else if c.toNat == 0x2028 then "\\u2028"
    else if c.toNat == 0x2029 then "\\u2029" else c.toString) ++ "\""

/-- Tokens with no space between them. A word is one token, except that the
parser reads `>=`, `>>`, `>>>`, `>>=` and `>>>=` as `>` and `=` tokens that
touch. -/
abbrev Word := List TokenKind

/-- A line: how many steps it is indented, and its words. -/
abbrev Line := Nat × List Word

def keywordWord (w : String) : Word := [.keyword w]
def identWord (n : String) : Word := [.ident n]
def punctWord (p : String) : Word := [.punct p]

/-- A line break inside a line. It is the empty word, because it has no
tokens. `render` ends the line there and writes the words after it on the
next line, further in. -/
def lineBreak : Word := []

/-- The line break between the callee and the `(` of a call: one after the
name `async`, as the standard needs, and none after any other callee. -/
def callBreak : Expr → List Word
  | .ident _ "async" => [lineBreak]
  | _ => []

/-- A property name after `.`, or a field name: a reserved word is a keyword
token, and any other name an identifier. -/
def propertyName (n : String) : Word :=
  if Lex.reservedWords.contains n then keywordWord n else identWord n

/-- An operator's symbol. A symbol that starts with `>` is its `>` and `=`
tokens, touching, and a word such as `instanceof` is a keyword. -/
def symbol (s : String) : Word :=
  if s.startsWith ">" then s.toList.map fun c => .punct c.toString
  else if Lex.reservedWords.contains s then keywordWord s
  else punctWord s

/-- `items`, with a `,` between two of them. -/
def commas : List (List Word) → List Word
  | [] => []
  | [item] => item
  | item :: rest => item ++ punctWord "," :: commas rest

/-- `items` between `open` and `close`, with a `,` between two of them. -/
def enclose (open_ close : String) (items : List (List Word)) : List Word :=
  punctWord open_ :: commas items ++ [punctWord close]

def LitType.words : LitType → List Word
  | .string value => [[.string value]]
  | .number text => [[.number text]]
  | .bigint text => [[.bigint text]]
  | .bool b => [keywordWord (if b then "true" else "false")]

mutual

def TypeExpr.words : TypeExpr → List Word
  | .keyword _ name => [if name == "void" then keywordWord name else identWord name]
  | .null _ => [keywordWord "null"]
  | .literal _ lit => lit.words
  | .ref _ name [] => [identWord name]
  | .ref _ name args => identWord name :: punctWord "<" :: commas (TypeExpr.wordsOf args) ++ [punctWord ">"]
  | .array _ elem => elem.words ++ [punctWord "[", punctWord "]"]
  -- A union of one member is `| T`, as `type A = | T` writes it.
  | .union _ [member] => punctWord "|" :: member.words
  | .union _ members => TypeExpr.bars (TypeExpr.wordsOf members)
  | .paren _ inner => punctWord "(" :: inner.words ++ [punctWord ")"]

def TypeExpr.wordsOf : List TypeExpr → List (List Word)
  | [] => []
  | t :: ts => t.words :: TypeExpr.wordsOf ts

/-- `members`, with a `|` between two of them. -/
def TypeExpr.bars : List (List Word) → List Word
  | [] => []
  | [member] => member
  | member :: rest => member ++ punctWord "|" :: TypeExpr.bars rest

end

def PropKey.words : PropKey → List Word
  | .ident name => [propertyName name]
  | .string value => [[.string value]]
  | .number text => [[.number text]]

mutual

def Expr.words : Expr → List Word
  | .ident _ name => [identWord name]
  | .number _ text => [[.number text]]
  | .bigint _ text => [[.bigint text]]
  | .string _ value => [[.string value]]
  | .bool _ b => [keywordWord (if b then "true" else "false")]
  | .null _ => [keywordWord "null"]
  | .array _ elems => enclose "[" "]" (Expr.wordsOf elems)
  | .object _ props => enclose "{" "}" (Property.wordsOf props)
  | .paren _ inner => punctWord "(" :: inner.words ++ [punctWord ")"]
  | .member _ obj name => obj.words ++ [punctWord ".", propertyName name]
  | .index _ obj idx => obj.words ++ punctWord "[" :: idx.words ++ [punctWord "]"]
  | .call _ callee args => callee.words ++ callBreak callee ++ enclose "(" ")" (Expr.wordsOf args)
  | .unary _ op arg => symbol op.symbol :: arg.words
  | .prefix _ op arg => punctWord op.symbol :: arg.words
  | .postfix _ op arg => arg.words ++ [punctWord op.symbol]
  | .binary _ op lhs rhs => lhs.words ++ symbol op.symbol :: rhs.words
  | .cond _ test a b => test.words ++ punctWord "?" :: a.words ++ punctWord ":" :: b.words
  | .assign _ op target value => target.words ++ symbol op.symbol :: value.words

def Expr.wordsOf : List Expr → List (List Word)
  | [] => []
  | e :: es => e.words :: Expr.wordsOf es

def Property.words : Property → List Word
  | .shorthand _ name => [identWord name]
  | .keyValue _ key value => key.words ++ punctWord ":" :: value.words

def Property.wordsOf : List Property → List (List Word)
  | [] => []
  | p :: ps => p.words :: Property.wordsOf ps

end

/-- `const` is a reserved word, and `let` an identifier. -/
def VarKind.word : VarKind → Word
  | .const => keywordWord "const"
  | .«let» => identWord "let"

def VarDecl.words (d : VarDecl) : List Word :=
  [d.kind.word, identWord d.name] ++
    (match d.type with | some t => punctWord ":" :: t.words | none => []) ++
    (match d.init with | some e => punctWord "=" :: e.words | none => []) ++ [punctWord ";"]

mutual

/-- The lines of a statement, `depth` steps in. -/
def Stmt.lines (depth : Nat) : Stmt → List Line
  | .varDecl _ d => [(depth, d.words)]
  | .exprStmt _ e => [(depth, e.words ++ [punctWord ";"])]
  | .returnStmt _ none => [(depth, [keywordWord "return", punctWord ";"])]
  | .returnStmt _ (some e) => [(depth, keywordWord "return" :: e.words ++ [punctWord ";"])]
  | .ifStmt _ test t none =>
    (depth, keywordWord "if" :: punctWord "(" :: test.words ++ [punctWord ")"]) :: t.lines (depth + 1)
  | .ifStmt _ test t (some e) =>
    (depth, keywordWord "if" :: punctWord "(" :: test.words ++ [punctWord ")"]) :: t.lines (depth + 1) ++
      (depth, [keywordWord "else"]) :: e.lines (depth + 1)
  | .forOfStmt _ kind name iterable body =>
    (depth, keywordWord "for" :: punctWord "(" :: kind.word :: identWord name :: identWord "of" :: iterable.words ++
      [punctWord ")"]) :: body.lines (depth + 1)
  | .whileStmt _ test body =>
    (depth, keywordWord "while" :: punctWord "(" :: test.words ++ [punctWord ")"]) :: body.lines (depth + 1)
  | .block _ body => (depth, [punctWord "{"]) :: Stmt.linesOf (depth + 1) body ++ [(depth, [punctWord "}"])]
  | .breakStmt _ => [(depth, [keywordWord "break", punctWord ";"])]
  | .continueStmt _ => [(depth, [keywordWord "continue", punctWord ";"])]
  | .empty _ => [(depth, [punctWord ";"])]

def Stmt.linesOf (depth : Nat) : List Stmt → List Line
  | [] => []
  | s :: ss => s.lines depth ++ Stmt.linesOf depth ss

end

def Param.words (p : Param) : List Word :=
  identWord p.name :: match p.type with | some t => punctWord ":" :: t.words | none => []

def Field.words (f : Field) : List Word :=
  (if f.readonly then [identWord "readonly"] else []) ++ [propertyName f.name] ++
    (if f.optional then [punctWord "?"] else []) ++ punctWord ":" :: f.type.words ++ [punctWord ";"]

def ImportName.words (n : ImportName) : List Word :=
  if n.typeOnly then [identWord "type", identWord n.name] else [identWord n.name]

def exportWords (exported : Bool) : List Word := if exported then [keywordWord "export"] else []

def Decl.lines : Decl → List Line
  | .import _ names source =>
    [(0, keywordWord "import" :: enclose "{" "}" (names.map ImportName.words) ++
      [identWord "from", [.string source], punctWord ";"])]
  | .function _ exported name params returnType body =>
    (0, exportWords exported ++ keywordWord "function" :: identWord name ::
      enclose "(" ")" (params.map Param.words) ++
      (match returnType with | some t => punctWord ":" :: t.words | none => [])) :: body.lines 0
  | .interface _ exported name fields =>
    (0, exportWords exported ++ [identWord "interface", identWord name, punctWord "{"]) ::
      fields.map (fun f => (1, f.words)) ++ [(0, [punctWord "}"])]
  | .typeAlias _ exported name type =>
    [(0, exportWords exported ++ identWord "type" :: identWord name :: punctWord "=" :: type.words ++ [punctWord ";"])]
  | .exportedVar _ d => [(0, keywordWord "export" :: d.words)]
  | .stmt s => s.lines 0

def Module.lines (m : Module) : List Line := m.decls.flatMap Decl.lines

/-! ### Rendering -/

def TokenKind.text : TokenKind → String
  | .ident s | .keyword s | .number s | .bigint s | .punct s => s
  | .string value => quote value
  | .eof => ""

def Word.text (w : Word) : String := String.join (w.map TokenKind.text)

/-- Words one space apart. At a `lineBreak`, the words after it go on a new
line that starts with `indent`. -/
def wordsText (indent : String) : List Word → String
  | [] => ""
  | [] :: ws => "\n" ++ indent ++ wordsText indent ws
  | [w] => Word.text w
  | w :: [] :: ws => Word.text w ++ wordsText indent ([] :: ws)
  | w :: ws => Word.text w ++ " " ++ wordsText indent ws

/-- A line as text, `2 * depth` spaces in. The rest of a line after a
`lineBreak` is two steps further in. -/
def Line.text (l : Line) : String :=
  "".pushn ' ' (2 * l.1) ++ wordsText ("".pushn ' ' (2 * l.1 + 4)) l.2

/-- The lines as source: each line ends in a line break. -/
def render (lines : List Line) : String := String.join (lines.map (·.text ++ "\n"))

/-- The module as source. -/
def Module.source (m : Module) : String := render m.lines

/-! ### Erasing spans -/

/-- The span that `erase` puts on every node. -/
def noSpan : Span := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩

mutual

def TypeExpr.erase : TypeExpr → TypeExpr
  | .keyword _ name => .keyword noSpan name
  | .null _ => .null noSpan
  | .literal _ lit => .literal noSpan lit
  | .ref _ name args => .ref noSpan name (TypeExpr.eraseAll args)
  | .array _ elem => .array noSpan elem.erase
  | .union _ members => .union noSpan (TypeExpr.eraseAll members)
  | .paren _ inner => .paren noSpan inner.erase

def TypeExpr.eraseAll : List TypeExpr → List TypeExpr
  | [] => []
  | t :: ts => t.erase :: TypeExpr.eraseAll ts

end

mutual

def Expr.erase : Expr → Expr
  | .ident _ name => .ident noSpan name
  | .number _ text => .number noSpan text
  | .bigint _ text => .bigint noSpan text
  | .string _ value => .string noSpan value
  | .bool _ b => .bool noSpan b
  | .null _ => .null noSpan
  | .array _ elems => .array noSpan (Expr.eraseAll elems)
  | .object _ props => .object noSpan (Property.eraseAll props)
  | .paren _ inner => .paren noSpan inner.erase
  | .member _ obj name => .member noSpan obj.erase name
  | .index _ obj idx => .index noSpan obj.erase idx.erase
  | .call _ callee args => .call noSpan callee.erase (Expr.eraseAll args)
  | .unary _ op arg => .unary noSpan op arg.erase
  | .prefix _ op arg => .prefix noSpan op arg.erase
  | .postfix _ op arg => .postfix noSpan op arg.erase
  | .binary _ op lhs rhs => .binary noSpan op lhs.erase rhs.erase
  | .cond _ test a b => .cond noSpan test.erase a.erase b.erase
  | .assign _ op target value => .assign noSpan op target.erase value.erase

def Expr.eraseAll : List Expr → List Expr
  | [] => []
  | e :: es => e.erase :: Expr.eraseAll es

def Property.erase : Property → Property
  | .shorthand _ name => .shorthand noSpan name
  | .keyValue _ key value => .keyValue noSpan key value.erase

def Property.eraseAll : List Property → List Property
  | [] => []
  | p :: ps => p.erase :: Property.eraseAll ps

end

def VarDecl.erase (d : VarDecl) : VarDecl :=
  { d with type := d.type.map TypeExpr.erase, init := d.init.map Expr.erase }

mutual

def Stmt.erase : Stmt → Stmt
  | .varDecl _ d => .varDecl noSpan d.erase
  | .exprStmt _ e => .exprStmt noSpan e.erase
  | .returnStmt _ v => .returnStmt noSpan (v.map Expr.erase)
  | .ifStmt _ test t e => .ifStmt noSpan test.erase t.erase (Stmt.eraseOpt e)
  | .forOfStmt _ kind name iterable body => .forOfStmt noSpan kind name iterable.erase body.erase
  | .whileStmt _ test body => .whileStmt noSpan test.erase body.erase
  | .block _ body => .block noSpan (Stmt.eraseAll body)
  | .breakStmt _ => .breakStmt noSpan
  | .continueStmt _ => .continueStmt noSpan
  | .empty _ => .empty noSpan

def Stmt.eraseOpt : Option Stmt → Option Stmt
  | none => none
  | some s => some s.erase

def Stmt.eraseAll : List Stmt → List Stmt
  | [] => []
  | s :: ss => s.erase :: Stmt.eraseAll ss

end

def Decl.erase : Decl → Decl
  | .import _ names source => .import noSpan (names.map fun n => { n with span := noSpan }) source
  | .function _ exported name params returnType body =>
    .function noSpan exported name (params.map fun p => { p with span := noSpan, type := p.type.map TypeExpr.erase })
      (returnType.map TypeExpr.erase) body.erase
  | .interface _ exported name fields =>
    .interface noSpan exported name (fields.map fun f => { f with span := noSpan, type := f.type.erase })
  | .typeAlias _ exported name type => .typeAlias noSpan exported name type.erase
  | .exportedVar _ d => .exportedVar noSpan d.erase
  | .stmt s => .stmt s.erase

def Module.erase (m : Module) : Module := { decls := m.decls.map Decl.erase }

/-! ### The round trip, on one module -/

/-- Parse `source`, print the tree, and parse the printed source: an error
unless the second tree is the first, apart from spans. -/
def roundTrip (source : String) (target : Edition := .default) : Except String Unit := do
  let m ← (parse source target).mapError (·.message)
  let printed := m.source
  let m' ← (parse printed target).mapError fun e =>
    s!"the printed source does not parse: {e.span.start.line}:{e.span.start.col}: {e.message}\n{printed}"
  unless Module.beq m'.erase m.erase do
    throw s!"the printed source parses as another tree:\n{printed}"

end tolean.TypeScript.Syntax
