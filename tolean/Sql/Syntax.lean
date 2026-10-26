import tolean.Source

/-!
The PostgreSQL front end: a lexer and a parser for the DDL that schema
migrations use and for the queries that sqlc reads.

Unquoted names fold to lower case, as in PostgreSQL. A statement that the
parser does not read is kept as its tokens (`Stmt.opaque`), so that the schema
translator can skip it when it does not touch a table it models, and refuse
it when it does.
-/
namespace tolean.Sql

open tolean

/-! ## Tokens -/

inductive TokenKind where
  /-- A name or a key word, folded to lower case unless it was quoted. -/
  | word (text : String) (quoted : Bool)
  | number (text : String)
  | string (value : String)
  /-- The body of a `$$…$$` or `$tag$…$tag$` string. -/
  | dollar (body : String)
  | punct (symbol : String)
  | eof
deriving Repr, BEq, Inhabited

structure Token where
  kind : TokenKind
  span : Span
deriving Repr, Inhabited

def TokenKind.describe : TokenKind → String
  | .word t _ => s!"'{t}'"
  | .number t => s!"number {t}"
  | .string _ => "a string"
  | .dollar _ => "a dollar-quoted string"
  | .punct p => s!"'{p}'"
  | .eof => "the end of the input"

/-- The token is the unquoted key word `w`. -/
def Token.isWord (t : Token) (w : String) : Bool := t.kind == .word w false
def Token.isPunct (t : Token) (p : String) : Bool := t.kind == .punct p

/-! ## Lexer -/

structure LexState where
  src : Array Char
  i : Nat := 0
  line : Nat := 1
  col : Nat := 1
  tokens : Array Token := #[]

abbrev LexM := EStateM ParseError LexState

namespace Lex

def punctuators : List String :=
  ["::", "->>", "->", "<=", ">=", "<>", "!=", "||",
   "(", ")", ",", ";", ".", "=", "<", ">", "+", "-", "*", "/", "%", "[", "]", ":"]

def peekChar (k : Nat := 0) : LexM (Option Char) := do
  let s ← get
  return s.src[s.i + k]?

def here : LexM Pos := do
  let s ← get
  return ⟨s.line, s.col⟩

def failFrom {A : Type} (start : Pos) (message : String) : LexM A := do
  throw ({ span := ⟨start, ← here⟩, message } : ParseError)

def advanceChar : LexM Unit :=
  modify fun s =>
    if s.src[s.i]? == some '\n' then { s with i := s.i + 1, line := s.line + 1, col := 1 }
    else { s with i := s.i + 1, col := s.col + 1 }

partial def skipTrivia : LexM Unit := do
  match ← peekChar, ← peekChar 1 with
  | some c, _ =>
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
      advanceChar
      skipTrivia
    else if c == '-' && (← peekChar 1) == some '-' then
      repeat
        match ← peekChar with
        | some '\n' | none => break
        | some _ => advanceChar
      skipTrivia
    else if c == '/' && (← peekChar 1) == some '*' then
      let start ← here
      advanceChar
      advanceChar
      repeat
        match ← peekChar, ← peekChar 1 with
        | some '*', some '/' =>
          advanceChar
          advanceChar
          break
        | some _, _ => advanceChar
        | none, _ => failFrom start "unterminated comment"
      skipTrivia
    else return
  | none, _ => return

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentPart (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

partial def takeWhile (p : Char → Bool) (acc : String) : LexM String := do
  match ← peekChar with
  | some c => if p c then advanceChar; takeWhile p (acc.push c) else return acc
  | none => return acc

/-- A `'…'` string, after the opening quote; `''` is one quote. -/
partial def readString (start : Pos) (acc : String) : LexM String := do
  match ← peekChar with
  | none => failFrom start "unterminated string"
  | some '\'' =>
    advanceChar
    if (← peekChar) == some '\'' then
      advanceChar
      readString start (acc.push '\'')
    else return acc
  | some c =>
    advanceChar
    readString start (acc.push c)

partial def readQuotedIdent (start : Pos) (acc : String) : LexM String := do
  match ← peekChar with
  | none => failFrom start "unterminated quoted name"
  | some '"' =>
    advanceChar
    if (← peekChar) == some '"' then
      advanceChar
      readQuotedIdent start (acc.push '"')
    else return acc
  | some c =>
    advanceChar
    readQuotedIdent start (acc.push c)

def matchesAt (src : Array Char) (i : Nat) : List Char → Bool
  | [] => true
  | c :: cs => src[i]? == some c && matchesAt src (i + 1) cs

/-- A dollar-quoted string, at its first `$`. -/
partial def readDollar (start : Pos) : LexM String := do
  advanceChar
  let tag ← takeWhile isIdentPart ""
  if (← peekChar) != some '$' then failFrom start "expected '$' to open a dollar-quoted string"
  advanceChar
  let close := ("$" ++ tag ++ "$").toList
  let mut body := ""
  repeat
    let s ← get
    if matchesAt s.src s.i close then
      for _ in close do advanceChar
      break
    match ← peekChar with
    | none => failFrom start "unterminated dollar-quoted string"
    | some c =>
      advanceChar
      body := body.push c
  return body

def lexKind (start : Pos) (c : Char) : LexM TokenKind := do
  if isIdentStart c then
    return .word (← takeWhile isIdentPart "").toLower false
  if c.isDigit then
    let whole ← takeWhile Char.isDigit ""
    if (← peekChar) == some '.' && (← peekChar 1).any Char.isDigit then
      advanceChar
      return .number (whole ++ "." ++ (← takeWhile Char.isDigit ""))
    return .number whole
  if c == '\'' then
    advanceChar
    return .string (← readString start "")
  if c == '"' then
    advanceChar
    return .word (← readQuotedIdent start "") true
  if c == '$' then
    if (← peekChar 1).any Char.isDigit then failFrom start "positional parameters are not supported"
    return .dollar (← readDollar start)
  let s ← get
  match punctuators.find? (fun p => matchesAt s.src s.i p.toList) with
  | some p =>
    for _ in [0:p.length] do advanceChar
    return .punct p
  | none =>
    -- Any other operator, such as `?` or `@>`: a token the parser refuses
    -- where it matters, so that the lexer can read the whole file.
    let isOp (c : Char) := "+-*/<>=~!@#%^&|`?".contains c
    if isOp c then return .punct (← takeWhile isOp "")
    failFrom start s!"unsupported character '{c}'"

partial def lexAll : LexM Unit := do
  skipTrivia
  let start ← here
  match ← peekChar with
  | none =>
    modify fun s => { s with tokens := s.tokens.push { kind := .eof, span := ⟨start, start⟩ } }
  | some c =>
    let kind ← lexKind start c
    let stop ← here
    modify fun s => { s with tokens := s.tokens.push { kind, span := ⟨start, stop⟩ } }
    lexAll

end Lex

def lex (source : String) : Except ParseError (Array Token) :=
  match Lex.lexAll.run { src := source.toList.toArray } with
  | .ok _ s => .ok s.tokens
  | .error e _ => .error e

/-! ## Syntax tree -/

/-- A type name as written, such as `bigint`, `timestamptz`, `text[]` or a
user type. Multi-word names are joined with spaces. -/
structure TypeName where
  name : String
  /-- `(n)` or `(p, s)` after the name. -/
  mods : List Nat := []
  array : Bool := false
deriving Repr, BEq, Inhabited

mutual

inductive Expr where
  | column (span : Span) (qualifier : Option String) (name : String)
  | int (span : Span) (value : Int)
  | str (span : Span) (value : String)
  | bool (span : Span) (value : Bool)
  | null (span : Span)
  /-- `sqlc.arg(name)` or `sqlc.narg(name)`. -/
  | arg (span : Span) (name : String) (nullable : Bool)
  | cast (span : Span) (e : Expr) (type : TypeName)
  /-- A literal with a type in front, such as `interval '34 days'`. -/
  | typedLit (span : Span) (type : TypeName) (value : String)
  | binary (span : Span) (op : String) (lhs rhs : Expr)
  | unary (span : Span) (op : String) (arg : Expr)
  | isNull (span : Span) (e : Expr) (negated : Bool)
  | call (span : Span) (name : String) (args : List Expr)
  | exists (span : Span) (q : Select)
  | subquery (span : Span) (q : Select)

/-- A table in `FROM`, joined to the earlier ones `on` a condition. -/
inductive FromItem where
  | mk (table : String) (alias : String) (on : Option Expr)

inductive SelectItem where
  | mk (e : Expr) (alias : Option String)

inductive Select where
  | mk (span : Span) (items : List SelectItem) (from_ : List FromItem) (where_ : Option Expr)
      (forUpdate : Bool)

end

instance : Inhabited Expr := ⟨.null default⟩

def Expr.span : Expr → Span
  | .column s .. | .int s .. | .str s .. | .bool s .. | .null s | .arg s .. | .cast s ..
  | .typedLit s .. | .binary s .. | .unary s .. | .isNull s .. | .call s .. | .exists s ..
  | .subquery s .. => s

def Select.span : Select → Span | .mk s .. => s

structure Update where
  span : Span
  table : String
  alias : String
  sets : List (String × Expr)
  from_ : List FromItem
  where_ : Option Expr
  returning : List SelectItem

inductive Body where
  | select (q : Select)
  | update (u : Update)

/-- `WITH name AS (…), …` then the main statement. -/
structure Query where
  ctes : List (String × Body)
  main : Body

inductive OnDelete where
  | noAction
  | cascade
  | restrict
  | setNull
deriving Repr, BEq, Inhabited

inductive ColumnConstraint where
  | notNull
  | null
  | default (e : Expr)
  | primaryKey
  | unique
  | references (table : String) (column : Option String) (onDelete : OnDelete)
  | check (e : Expr)

structure ColumnDef where
  name : String
  type : TypeName
  constraints : List ColumnConstraint

inductive TableConstraint where
  | primaryKey (columns : List String)
  | unique (columns : List String)
  | foreignKey (columns : List String) (table : String) (refColumns : List String) (onDelete : OnDelete)
  | check (e : Expr)

inductive AlterAction where
  | addColumn (c : ColumnDef) (ifNotExists : Bool)
  | dropColumn (name : String)
  | setType (column : String) (type : TypeName)
  | setDefault (column : String) (e : Expr)
  | dropDefault (column : String)
  | setNotNull (column : String)
  | dropNotNull (column : String)
  | addConstraint (name : Option String) (c : TableConstraint)
  | dropConstraint (name : String)

inductive Stmt where
  | createTable (span : Span) (name : String) (ifNotExists : Bool) (columns : List ColumnDef)
      (constraints : List (Option String × TableConstraint))
  /-- `CREATE TABLE … PARTITION OF parent`: storage only. -/
  | createPartition (span : Span) (name : String) (parent : String)
  | createEnum (span : Span) (name : String) (labels : List String)
  | createDomain (span : Span) (name : String) (type : TypeName)
  | alterTable (span : Span) (name : String) (actions : List AlterAction)
  | createIndex (span : Span) (unique : Bool) (name : String) (table : String)
      (columns : List String) (where_ : Option Expr)
  | drop (span : Span) (kind : String) (names : List String)
  | query (span : Span) (q : Query)
  /-- A statement the parser does not read, kept as its tokens. -/
  | opaque (span : Span) (tokens : List Token)

def Stmt.span : Stmt → Span
  | .createTable s .. | .createPartition s .. | .createEnum s .. | .createDomain s ..
  | .alterTable s .. | .createIndex s .. | .drop s .. | .query s .. | .opaque s .. => s

/-! ## Parser -/

structure ParseState where
  tokens : Array Token
  i : Nat := 0
  lastStop : Pos := ⟨1, 1⟩

abbrev ParseM := EStateM ParseError ParseState

namespace Parse

def peekAt (k : Nat) : ParseM Token := do
  let s ← get
  return s.tokens[min (s.i + k) (s.tokens.size - 1)]!

def peek : ParseM Token := peekAt 0

def advance : ParseM Token := do
  let s ← get
  let t := s.tokens[s.i]!
  set { s with i := min (s.i + 1) (s.tokens.size - 1), lastStop := t.span.stop }
  return t

def failAt {A : Type} (t : Token) (message : String) : ParseM A :=
  throw ({ span := t.span, message } : ParseError)

def unexpected {A : Type} (t : Token) (wanted : String) : ParseM A :=
  failAt t s!"expected {wanted}, found {t.kind.describe}"

def expectWord (w : String) : ParseM Token := do
  let t ← peek
  if t.isWord w then advance else unexpected t s!"'{w}'"

def expectPunct (p : String) : ParseM Token := do
  let t ← peek
  if t.isPunct p then advance else unexpected t s!"'{p}'"

def acceptWord (w : String) : ParseM Bool := do
  if (← peek).isWord w then
    discard advance
    return true
  return false

def acceptPunct (p : String) : ParseM Bool := do
  if (← peek).isPunct p then
    discard advance
    return true
  return false

def acceptWords (ws : List String) : ParseM Bool := do
  for w in ws, k in [0:ws.length] do
    if !(← peekAt k).isWord w then return false
  for _ in ws do discard advance
  return true

/-- Key words that cannot be a name in the place where they stand. -/
def reserved : List String :=
  ["select", "from", "where", "and", "or", "not", "join", "inner", "left", "right", "on",
   "as", "set", "returning", "for", "group", "order", "limit", "with", "is", "null", "union",
   "having", "using", "when", "then", "else", "end", "case", "in", "between", "like", "update",
   "insert", "delete", "values", "default", "check", "references", "primary", "unique",
   "constraint", "foreign", "cross", "full", "outer", "lateral", "offset", "fetch", "window"]

def readName : ParseM String := do
  let t ← advance
  match t.kind with
  | .word w quoted =>
    if !quoted && reserved.contains w then unexpected t "a name"
    return w
  | _ => unexpected t "a name"

/-- A name with an optional schema in front; the schema is dropped. -/
def readQualifiedName : ParseM String := do
  let n ← readName
  if (← peek).isPunct "." then
    discard advance
    return ← readName
  return n

def readNameList : ParseM (List String) := do
  discard (expectPunct "(")
  let mut names := #[← readName]
  while ← acceptPunct "," do names := names.push (← readName)
  discard (expectPunct ")")
  return names.toList

def readNat : ParseM Nat := do
  let t ← advance
  match t.kind with
  | .number n => match n.toNat? with
    | some v => return v
    | none => unexpected t "a whole number"
  | _ => unexpected t "a number"

def multiWordTypes : List (List String) :=
  [["double", "precision"], ["timestamp", "with", "time", "zone"],
   ["timestamp", "without", "time", "zone"], ["character", "varying"],
   ["time", "with", "time", "zone"]]

def readTypeName : ParseM TypeName := do
  let mut name := ""
  for ws in multiWordTypes do
    if name.isEmpty && (← acceptWords ws) then name := " ".intercalate ws
  if name.isEmpty then name ← readQualifiedName
  let mut mods := []
  if (← peek).isPunct "(" then
    discard advance
    let mut ns := #[← readNat]
    while ← acceptPunct "," do ns := ns.push (← readNat)
    discard (expectPunct ")")
    mods := ns.toList
  let mut array := false
  if (← peek).isPunct "[" then
    discard advance
    discard (expectPunct "]")
    array := true
  return { name, mods, array }

def compareOps : List String := ["=", "<>", "!=", "<", ">", "<=", ">="]

mutual

partial def parseExpr : ParseM Expr := parseOr

partial def parseOr : ParseM Expr := do
  let mut lhs ← parseAnd
  while (← peek).isWord "or" do
    discard advance
    let rhs ← parseAnd
    lhs := .binary ⟨lhs.span.start, rhs.span.stop⟩ "or" lhs rhs
  return lhs

partial def parseAnd : ParseM Expr := do
  let mut lhs ← parseNot
  while (← peek).isWord "and" do
    discard advance
    let rhs ← parseNot
    lhs := .binary ⟨lhs.span.start, rhs.span.stop⟩ "and" lhs rhs
  return lhs

partial def parseNot : ParseM Expr := do
  let t ← peek
  if t.isWord "not" then
    discard advance
    let arg ← parseNot
    return .unary ⟨t.span.start, arg.span.stop⟩ "not" arg
  parseIs

partial def parseIs : ParseM Expr := do
  let lhs ← parseCompare
  if (← peek).isWord "is" then
    discard advance
    let negated ← acceptWord "not"
    discard (expectWord "null")
    return .isNull ⟨lhs.span.start, (← get).lastStop⟩ lhs negated
  return lhs

partial def parseCompare : ParseM Expr := do
  let lhs ← parseAdd
  let t ← peek
  match t.kind with
  | .punct op =>
    if compareOps.contains op then
      discard advance
      let rhs ← parseAdd
      return .binary ⟨lhs.span.start, rhs.span.stop⟩ (if op == "!=" then "<>" else op) lhs rhs
    return lhs
  | .word w false =>
    if ["in", "between", "like", "ilike", "similar"].contains w then
      failAt t s!"'{w}' is not supported"
    return lhs
  | _ => return lhs

partial def parseAdd : ParseM Expr := do
  let mut lhs ← parseMul
  repeat
    let t ← peek
    match t.kind with
    | .punct op =>
      if op == "+" || op == "-" || op == "||" then
        discard advance
        let rhs ← parseMul
        lhs := .binary ⟨lhs.span.start, rhs.span.stop⟩ op lhs rhs
      else break
    | _ => break
  return lhs

partial def parseMul : ParseM Expr := do
  let mut lhs ← parseUnary
  repeat
    let t ← peek
    match t.kind with
    | .punct op =>
      if op == "*" || op == "/" || op == "%" then
        discard advance
        let rhs ← parseUnary
        lhs := .binary ⟨lhs.span.start, rhs.span.stop⟩ op lhs rhs
      else break
    | _ => break
  return lhs

partial def parseUnary : ParseM Expr := do
  let t ← peek
  if t.isPunct "-" then
    discard advance
    let arg ← parseUnary
    return .unary ⟨t.span.start, arg.span.stop⟩ "-" arg
  parsePostfix

partial def parsePostfix : ParseM Expr := do
  let mut e ← parsePrimary
  repeat
    let t ← peek
    if t.isPunct "::" then
      discard advance
      let ty ← readTypeName
      e := .cast ⟨e.span.start, (← get).lastStop⟩ e ty
    else if t.isPunct "->>" || t.isPunct "->" then
      failAt t "JSON operators are not supported"
    else break
  return e

partial def parseArgs : ParseM (List Expr) := do
  discard (expectPunct "(")
  if ← acceptPunct ")" then return []
  let mut args := #[← parseExpr]
  while ← acceptPunct "," do args := args.push (← parseExpr)
  discard (expectPunct ")")
  return args.toList

partial def parsePrimary : ParseM Expr := do
  let t ← peek
  match t.kind with
  | .number n =>
    discard advance
    match n.toInt? with
    | some v => return .int t.span v
    | none => failAt t "decimal literals are not supported"
  | .string v =>
    discard advance
    return .str t.span v
  | .punct "(" =>
    discard advance
    if (← peek).isWord "select" then
      let q ← parseSelect
      discard (expectPunct ")")
      return .subquery ⟨t.span.start, (← get).lastStop⟩ q
    let e ← parseExpr
    discard (expectPunct ")")
    return e
  | .word w quoted =>
    if !quoted then
      match w with
      | "null" => discard advance; return .null t.span
      | "true" => discard advance; return .bool t.span true
      | "false" => discard advance; return .bool t.span false
      | "exists" =>
        discard advance
        discard (expectPunct "(")
        let q ← parseSelect
        discard (expectPunct ")")
        return .exists ⟨t.span.start, (← get).lastStop⟩ q
      | "case" => failAt t "CASE is not supported"
      | "interval" | "timestamptz" | "timestamp" | "date" =>
        if let .string v := (← peekAt 1).kind then
          discard advance
          discard advance
          return .typedLit ⟨t.span.start, (← get).lastStop⟩ { name := w } v
      | _ => pure ()
    discard advance
    -- `sqlc.arg(name)`, `sqlc.narg(name)`
    if w == "sqlc" && (← peek).isPunct "." then
      discard advance
      let fn ← readName
      discard (expectPunct "(")
      let name ← readName
      discard (expectPunct ")")
      if fn != "arg" && fn != "narg" then failAt t s!"sqlc.{fn} is not supported"
      return .arg ⟨t.span.start, (← get).lastStop⟩ name (fn == "narg")
    if (← peek).isPunct "(" then
      let args ← parseArgs
      return .call ⟨t.span.start, (← get).lastStop⟩ w args
    if (← peek).isPunct "." then
      discard advance
      let (col, stop) ← do
        let c ← advance
        match c.kind with
        | .word n _ => pure (n, c.span.stop)
        | .punct "*" => failAt c "'*' is not supported"
        | _ => unexpected c "a column"
      return .column ⟨t.span.start, stop⟩ (some w) col
    if reserved.contains w && !quoted then unexpected t "an expression"
    return .column t.span none w
  | _ => unexpected t "an expression"

partial def parseFrom : ParseM (List FromItem) := do
  let readItem (on : Option Expr) : ParseM FromItem := do
    let table ← readQualifiedName
    discard (acceptWord "as")
    let t ← peek
    let alias ← match t.kind with
      | .word w false => if reserved.contains w then pure table else readName
      | .word _ true => readName
      | _ => pure table
    return .mk table alias on
  let mut items := #[← readItem none]
  repeat
    let t ← peek
    if t.isPunct "," then
      discard advance
      items := items.push (← readItem none)
    else if t.isWord "join" || t.isWord "inner" then
      discard advance
      if t.isWord "inner" then discard (expectWord "join")
      let table ← readQualifiedName
      discard (acceptWord "as")
      let alias ← if (← peek).isWord "on" then pure table else readName
      discard (expectWord "on")
      let cond ← parseExpr
      items := items.push (.mk table alias (some cond))
    else if t.isWord "left" || t.isWord "right" || t.isWord "full" || t.isWord "cross" then
      failAt t s!"{t.kind.describe} joins are not supported"
    else break
  return items.toList

partial def parseSelectItems : ParseM (List SelectItem) := do
  let readItem : ParseM SelectItem := do
    let e ← parseExpr
    let alias ← if ← acceptWord "as" then some <$> readName else pure none
    return .mk e alias
  let mut items := #[← readItem]
  while ← acceptPunct "," do items := items.push (← readItem)
  return items.toList

partial def parseSelect : ParseM Select := do
  let kw ← expectWord "select"
  if (← peek).isWord "distinct" then failAt (← peek) "DISTINCT is not supported"
  let items ← parseSelectItems
  let from_ ← if ← acceptWord "from" then parseFrom else pure []
  let where_ ← if ← acceptWord "where" then some <$> parseExpr else pure none
  for w in ["group", "order", "limit", "offset", "having", "union"] do
    if (← peek).isWord w then failAt (← peek) s!"'{w}' is not supported"
  let mut forUpdate := false
  if ← acceptWords ["for", "update"] then
    forUpdate := true
    if ← acceptWord "of" then
      discard readName
      while ← acceptPunct "," do discard readName
  return .mk ⟨kw.span.start, (← get).lastStop⟩ items from_ where_ forUpdate

end

def parseUpdate : ParseM Update := do
  let kw ← expectWord "update"
  let table ← readQualifiedName
  discard (acceptWord "as")
  let alias ← if (← peek).isWord "set" then pure table else readName
  discard (expectWord "set")
  let readSet : ParseM (String × Expr) := do
    let col ← readName
    discard (expectPunct "=")
    return (col, ← parseExpr)
  let mut sets := #[← readSet]
  while ← acceptPunct "," do sets := sets.push (← readSet)
  let from_ ← if ← acceptWord "from" then parseFrom else pure []
  let where_ ← if ← acceptWord "where" then some <$> parseExpr else pure none
  let returning ← if ← acceptWord "returning" then parseSelectItems else pure []
  return { span := ⟨kw.span.start, (← get).lastStop⟩, table, alias, sets := sets.toList, from_,
           where_, returning }

def parseBody : ParseM Body := do
  let t ← peek
  if t.isWord "select" then return .select (← parseSelect)
  if t.isWord "update" then return .update (← parseUpdate)
  if t.isWord "insert" || t.isWord "delete" then failAt t s!"{t.kind.describe} is not supported yet"
  unexpected t "SELECT or UPDATE"

def parseQuery : ParseM Query := do
  let mut ctes := #[]
  if ← acceptWord "with" then
    if (← peek).isWord "recursive" then failAt (← peek) "WITH RECURSIVE is not supported"
    repeat
      let name ← readName
      discard (expectWord "as")
      discard (expectPunct "(")
      let body ← parseBody
      discard (expectPunct ")")
      ctes := ctes.push (name, body)
      if !(← acceptPunct ",") then break
  return { ctes := ctes.toList, main := ← parseBody }

def parseOnDelete : ParseM OnDelete := do
  if ← acceptWords ["on", "delete"] then
    if ← acceptWord "cascade" then return .cascade
    if ← acceptWord "restrict" then return .restrict
    if ← acceptWords ["set", "null"] then return .setNull
    if ← acceptWords ["no", "action"] then return .noAction
    unexpected (← peek) "a delete action"
  return .noAction

def parseColumnConstraints : ParseM (List ColumnConstraint) := do
  let mut cs := #[]
  repeat
    if ← acceptWord "constraint" then discard readName
    if ← acceptWords ["not", "null"] then cs := cs.push .notNull
    else if ← acceptWord "null" then cs := cs.push .null
    else if ← acceptWord "default" then cs := cs.push (.default (← parseExpr))
    else if ← acceptWords ["primary", "key"] then cs := cs.push .primaryKey
    else if ← acceptWord "unique" then cs := cs.push .unique
    else if ← acceptWord "references" then
      let table ← readQualifiedName
      let col ← if (← peek).isPunct "(" then do
          let ns ← readNameList
          pure ns.head?
        else pure none
      cs := cs.push (.references table col (← parseOnDelete))
    else if ← acceptWord "check" then
      discard (expectPunct "(")
      let e ← parseExpr
      discard (expectPunct ")")
      cs := cs.push (.check e)
    else break
  return cs.toList

def parseColumnDef : ParseM ColumnDef := do
  let name ← readName
  let type ← readTypeName
  return { name, type, constraints := ← parseColumnConstraints }

def parseTableConstraint : ParseM TableConstraint := do
  if ← acceptWords ["primary", "key"] then return .primaryKey (← readNameList)
  if ← acceptWord "unique" then return .unique (← readNameList)
  if ← acceptWords ["foreign", "key"] then
    let cols ← readNameList
    discard (expectWord "references")
    let table ← readQualifiedName
    let refCols ← if (← peek).isPunct "(" then readNameList else pure []
    return .foreignKey cols table refCols (← parseOnDelete)
  if ← acceptWord "check" then
    discard (expectPunct "(")
    let e ← parseExpr
    discard (expectPunct ")")
    return .check e
  unexpected (← peek) "a table constraint"

def startsTableConstraint (t : Token) : Bool :=
  t.isWord "constraint" || t.isWord "primary" || t.isWord "unique" || t.isWord "foreign" ||
    t.isWord "check"

def parseCreateTable (start : Pos) : ParseM Stmt := do
  let ifNotExists ← acceptWords ["if", "not", "exists"]
  let name ← readQualifiedName
  if ← acceptWords ["partition", "of"] then
    let parent ← readQualifiedName
    -- `DEFAULT` or `FOR VALUES …`: storage only.
    while !(← peek).isPunct ";" && !((← peek).kind == .eof) do discard advance
    return .createPartition ⟨start, (← get).lastStop⟩ name parent
  discard (expectPunct "(")
  let mut columns := #[]
  let mut constraints := #[]
  repeat
    if startsTableConstraint (← peek) then
      let cname ← if ← acceptWord "constraint" then some <$> readName else pure none
      constraints := constraints.push (cname, ← parseTableConstraint)
    else columns := columns.push (← parseColumnDef)
    if !(← acceptPunct ",") then break
  discard (expectPunct ")")
  if ← acceptWords ["partition", "by"] then
    -- How rows are stored, not what they mean.
    discard readName
    discard (expectPunct "(")
    let mut depth := 1
    while depth > 0 do
      let t ← advance
      if t.isPunct "(" then depth := depth + 1
      if t.isPunct ")" then depth := depth - 1
      if t.kind == .eof then failAt t "unterminated PARTITION BY"
  return .createTable ⟨start, (← get).lastStop⟩ name ifNotExists columns.toList constraints.toList

def parseAlterAction : ParseM AlterAction := do
  if ← acceptWord "add" then
    if (← peek).isWord "constraint" || startsTableConstraint (← peek) then
      let cname ← if ← acceptWord "constraint" then some <$> readName else pure none
      return .addConstraint cname (← parseTableConstraint)
    discard (acceptWord "column")
    let ifNotExists ← acceptWords ["if", "not", "exists"]
    return .addColumn (← parseColumnDef) ifNotExists
  if ← acceptWord "drop" then
    if ← acceptWord "constraint" then
      discard (acceptWords ["if", "exists"])
      return .dropConstraint (← readName)
    discard (acceptWord "column")
    discard (acceptWords ["if", "exists"])
    return .dropColumn (← readName)
  if ← acceptWord "alter" then
    discard (acceptWord "column")
    let col ← readName
    if ← acceptWords ["set", "data", "type"] then return .setType col (← readTypeName)
    if ← acceptWord "type" then
      let ty ← readTypeName
      if (← peek).isWord "using" then failAt (← peek) "ALTER COLUMN … USING is not supported"
      return .setType col ty
    if ← acceptWords ["set", "default"] then return .setDefault col (← parseExpr)
    if ← acceptWords ["drop", "default"] then return .dropDefault col
    if ← acceptWords ["set", "not", "null"] then return .setNotNull col
    if ← acceptWords ["drop", "not", "null"] then return .dropNotNull col
    unexpected (← peek) "a column change"
  unexpected (← peek) "ADD, DROP or ALTER"

def parseStmtTokens : ParseM Stmt := do
  let t ← peek
  let start := t.span.start
  if ← acceptWord "create" then
    let _ ← acceptWords ["or", "replace"]
    if ← acceptWord "table" then return ← parseCreateTable start
    if ← acceptWord "type" then
      let name ← readQualifiedName
      discard (expectWord "as")
      discard (expectWord "enum")
      discard (expectPunct "(")
      let mut labels := #[]
      repeat
        let l ← advance
        match l.kind with
        | .string v => labels := labels.push v
        | _ => unexpected l "an enum label"
        if !(← acceptPunct ",") then break
      discard (expectPunct ")")
      return .createEnum ⟨start, (← get).lastStop⟩ name labels.toList
    if ← acceptWord "domain" then
      let name ← readQualifiedName
      discard (expectWord "as")
      let ty ← readTypeName
      if (← peek).isWord "check" || (← peek).isWord "not" || (← peek).isWord "constraint" then
        failAt (← peek) "domain constraints are not supported"
      return .createDomain ⟨start, (← get).lastStop⟩ name ty
    let unique ← acceptWord "unique"
    if ← acceptWord "index" then
      discard (acceptWord "concurrently")
      discard (acceptWords ["if", "not", "exists"])
      let name ← readName
      discard (expectWord "on")
      let table ← readQualifiedName
      if ← acceptWord "using" then discard readName
      discard (expectPunct "(")
      let mut cols := #[]
      repeat
        let c ← peek
        match c.kind with
        | .word w false =>
          if (← peekAt 1).isPunct "(" then failAt c "expression indexes are not supported"
          discard advance
          cols := cols.push w
        | .word w true => discard advance; cols := cols.push w
        | _ => unexpected c "an index column"
        -- Sort order and nulls order do not change which rows are unique.
        discard (acceptWord "asc" <||> acceptWord "desc")
        discard (acceptWords ["nulls", "first"] <||> acceptWords ["nulls", "last"])
        if !(← acceptPunct ",") then break
      discard (expectPunct ")")
      let where_ ← if ← acceptWord "where" then some <$> parseExpr else pure none
      return .createIndex ⟨start, (← get).lastStop⟩ unique name table cols.toList where_
    failAt t "this CREATE statement is not supported"
  if ← acceptWord "alter" then
    if ← acceptWord "table" then
      discard (acceptWords ["if", "exists"])
      discard (acceptWord "only")
      let name ← readQualifiedName
      let mut actions := #[← parseAlterAction]
      while ← acceptPunct "," do actions := actions.push (← parseAlterAction)
      return .alterTable ⟨start, (← get).lastStop⟩ name actions.toList
    failAt t "this ALTER statement is not supported"
  if ← acceptWord "drop" then
    let kind ← readName
    discard (acceptWord "concurrently")
    discard (acceptWords ["if", "exists"])
    let mut names := #[← readQualifiedName]
    while ← acceptPunct "," do names := names.push (← readQualifiedName)
    discard (acceptWord "cascade" <||> acceptWord "restrict")
    return .drop ⟨start, (← get).lastStop⟩ kind names.toList
  if t.isWord "select" || t.isWord "update" || t.isWord "with" then
    let q ← parseQuery
    return .query ⟨start, (← get).lastStop⟩ q
  failAt t "this statement is not supported"

end Parse

/-- The statements of `source`, split at top-level `;`. A statement that does
not parse is kept as `Stmt.opaque` with its tokens, together with the reason. -/
def parseStatements (source : String) : Except ParseError (List (Stmt × Option ParseError)) := do
  let tokens ← lex source
  let mut out := #[]
  let mut current : Array Token := #[]
  for t in tokens do
    if t.isPunct ";" || t.kind == .eof then
      if !current.isEmpty then
        let span : Span := ⟨current[0]!.span.start, current.back!.span.stop⟩
        let eofTok : Token := { kind := .eof, span := ⟨span.stop, span.stop⟩ }
        match (Parse.parseStmtTokens <* (do
            let t ← Parse.peek
            if t.kind != .eof then Parse.unexpected t "the end of the statement")).run
            { tokens := current.push eofTok } with
        | .ok s _ => out := out.push (s, none)
        | .error e _ => out := out.push (.opaque span current.toList, some e)
      current := #[]
    else current := current.push t
  return out.toList

/-- A sqlc query file: each `-- name: Name :kind` comment names the statement
that follows it. -/
structure NamedQuery where
  name : String
  /-- `one`, `many`, `exec`, `execrows` or `batchone`. -/
  kind : String
  line : Nat
  source : String

def splitNamedQueries (source : String) : List NamedQuery := Id.run do
  let lines := source.splitOn "\n"
  let mut out : Array NamedQuery := #[]
  let mut current : Option NamedQuery := none
  for (line, k) in lines.zipIdx do
    let trimmed := line.trimAscii.toString
    if trimmed.startsWith "-- name:" then
      if let some q := current then out := out.push q
      let parts := ((trimmed.drop 8).toString.splitOn " ").filter (· != "")
      let name := parts.head?.getD ""
      let kind := ((parts[1]?.getD ":one").drop 1).toString
      current := some { name, kind, line := k + 2, source := "" }
    else if let some q := current then
      current := some { q with source := q.source ++ line ++ "\n" }
  if let some q := current then out := out.push q
  return out.toList

end tolean.Sql
