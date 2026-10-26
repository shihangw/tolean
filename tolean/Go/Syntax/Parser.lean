import tolean.Go.Syntax.Ast
import tolean.Go.Syntax.Lexer

/-!
The Go parser: recursive descent, with precedence climbing for binary
operators, as `go/parser` reads Go. Every node gets the span `go/ast` gives it.

It reads the part of Go that Tolean supports, and refuses everything else
with a position and a reason: generics, channels, `go`, `goto`, `select`,
labels and `fallthrough`. It reads some syntax that the translator refuses,
such as type switches, function literals and `defer`, so that a file can be
read when only some of its declarations are translated.

As in `go/parser`, a composite literal whose type is a plain type name cannot
stand in the header of `if`, `for` or `switch` unless it is in parentheses:
there, `T {` starts the block.
-/
namespace tolean.Go.Syntax

open tolean

structure ParseState where
  tokens : Array Token
  i : Nat := 0
  /-- The end of the last token read. -/
  lastStop : Pos := ⟨1, 1⟩
  /-- Below zero in the header of `if`, `for` and `switch`; see the module
  comment. Each open `(`, `[` or `{` raises it by one, as in `go/parser`. -/
  exprLev : Int := 0

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

def expectPunct (symbol : String) : ParseM Token := do
  let t ← peek
  if t.isPunct symbol then advance else unexpected t s!"'{symbol}'"

def expectKeyword (word : String) : ParseM Token := do
  let t ← peek
  if t.isKeyword word then advance else unexpected t s!"'{word}'"

def readIdent : ParseM (String × Span) := do
  let t ← advance
  match t.kind with
  | .ident name => return (name, t.span)
  | _ => unexpected t "a name"

/-- End a statement, a spec or a field. Go lets the `;` go before `)` and
`}`. -/
def expectSemi : ParseM Unit := do
  let t ← peek
  if t.isSemi then discard advance
  else if t.isPunct ")" || t.isPunct "}" || t.isEof then return
  else unexpected t "';' or a line break"

def withExprLev {A : Type} (lev : Int) (body : ParseM A) : ParseM A := do
  let saved := (← get).exprLev
  modify fun s => { s with exprLev := lev }
  let result ← body
  modify fun s => { s with exprLev := saved }
  return result

def nested {A : Type} (body : ParseM A) : ParseM A := do
  withExprLev ((← get).exprLev + 1) body

def binaryPrec (t : Token) : Option Nat :=
  match t.kind with
  | .punct "||" => some 1
  | .punct "&&" => some 2
  | .punct "==" | .punct "!=" | .punct "<" | .punct "<=" | .punct ">" | .punct ">=" => some 3
  | .punct "+" | .punct "-" | .punct "|" | .punct "^" => some 4
  | .punct "*" | .punct "/" | .punct "%" | .punct "<<" | .punct ">>" | .punct "&"
  | .punct "&^" => some 5
  | _ => none

def assignOps : List String :=
  ["=", ":=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "&^="]

/-- A token that can start a type. -/
def startsType (t : Token) : Bool :=
  match t.kind with
  | .ident _ => true
  | .punct "*" | .punct "[" | .punct "(" => true
  | .keyword "map" | .keyword "struct" | .keyword "interface" | .keyword "func" => true
  | _ => false

def isTypeName : Expr → Bool
  | .ident .. => true
  | .selector _ (.ident ..) _ => true
  | _ => false

def isLiteralType : Expr → Bool
  | .arrayType .. | .sliceType .. | .structType .. | .mapType .. => true
  | e => isTypeName e

def refuseKeyword (t : Token) : ParseM Unit := do
  match t.kind with
  | .keyword "chan" => failAt t "channels are not supported"
  | .keyword "go" => failAt t "'go' statements are not supported"
  | .keyword "goto" => failAt t "'goto' is not supported"
  | .keyword "select" => failAt t "'select' is not supported"
  | .keyword "fallthrough" => failAt t "'fallthrough' is not supported"
  | _ => return

/-- Turn a parameter list into fields. Either every entry is a type, or the
entries are names followed by a type, as in `a, b int, c string`. -/
def groupParams (items : Array (Expr × Option Expr)) : ParseM (List Field) := do
  if items.all (·.2.isNone) then
    return items.toList.map fun (t, _) => .mk t.span [] t none
  let mut fields : Array Field := #[]
  let mut pending : Array (String × Span) := #[]
  for (first, type?) in items do
    let name ← match first with
      | .ident s n => pure (n, s)
      | e => throw ({ span := e.span, message := "expected a parameter name" } : ParseError)
    match type? with
    | none => pending := pending.push name
    | some ty =>
      let names := pending.push name
      fields := fields.push (.mk ⟨names[0]!.2.start, ty.span.stop⟩ (names.toList.map (·.1)) ty none)
      pending := #[]
  if h : 0 < pending.size then
    throw ({ span := pending[0].2, message := "a parameter needs a type" } : ParseError)
  return fields.toList

/-- A simple statement, or the head of a `range` clause. -/
inductive Simple where
  | stmt (s : Stmt)
  | range (op : String) (lhs : List Expr) (iterable : Expr)

mutual

-- Types

partial def parseType : ParseM Expr := do
  let t ← peek
  refuseKeyword t
  match t.kind with
  | .ident _ =>
    let (name, span) ← readIdent
    let base := Expr.ident span name
    if (← peek).isPunct "." then
      discard advance
      let (sel, selSpan) ← readIdent
      return .selector ⟨span.start, selSpan.stop⟩ base sel
    return base
  | .punct "*" =>
    discard advance
    let inner ← parseType
    return .star ⟨t.span.start, inner.span.stop⟩ inner
  | .punct "(" =>
    discard advance
    let inner ← nested parseType
    discard (expectPunct ")")
    return .paren ⟨t.span.start, (← get).lastStop⟩ inner
  | .punct "[" => parseArrayOrSliceType
  | .keyword "map" => parseMapType
  | .keyword "struct" => parseStructType
  | .keyword "interface" => parseInterfaceType
  | .keyword "func" =>
    discard advance
    parseSignatureType t.span.start
  | _ => unexpected t "a type"

partial def parseArrayOrSliceType : ParseM Expr := do
  let lb ← expectPunct "["
  if (← peek).isPunct "]" then
    discard advance
    let elem ← parseType
    return .sliceType ⟨lb.span.start, elem.span.stop⟩ elem
  if (← peek).isPunct "..." then failAt (← peek) "[...]T array types are not supported"
  let len ← nested parseExpr
  discard (expectPunct "]")
  let elem ← parseType
  return .arrayType ⟨lb.span.start, elem.span.stop⟩ len elem

partial def parseMapType : ParseM Expr := do
  let kw ← expectKeyword "map"
  discard (expectPunct "[")
  let key ← nested parseType
  discard (expectPunct "]")
  let value ← parseType
  return .mapType ⟨kw.span.start, value.span.stop⟩ key value

partial def parseTag : ParseM (Option Expr) := do
  let t ← peek
  match t.kind with
  | .lit .string raw =>
    discard advance
    return some (.lit t.span .string raw)
  | _ => return none

partial def parseStructField : ParseM Field := do
  let t ← peek
  let start := t.span.start
  let (names, type) ← match t.kind with
    | .ident _ =>
      let next ← peekAt 1
      if next.isPunct "," then
        let mut names := #[(← readIdent).1]
        while (← peek).isPunct "," do
          discard advance
          names := names.push (← readIdent).1
        pure (names.toList, ← parseType)
      else if next.isPunct "." || next.isSemi || next.isPunct "}" ||
          (next.kind matches .lit .string _) then
        pure ([], ← parseType)
      else
        let (name, _) ← readIdent
        pure ([name], ← parseType)
    | .punct "*" => pure ([], ← parseType)
    | _ => unexpected t "a field"
  let tag ← parseTag
  let stop := (tag.map Expr.span).getD type.span |>.stop
  return .mk ⟨start, stop⟩ names type tag

partial def parseStructType : ParseM Expr := do
  let kw ← expectKeyword "struct"
  discard (expectPunct "{")
  let mut fields := #[]
  while !(← peek).isPunct "}" do
    fields := fields.push (← nested parseStructField)
    expectSemi
  discard (expectPunct "}")
  return .structType ⟨kw.span.start, (← get).lastStop⟩ fields.toList

partial def parseInterfaceType : ParseM Expr := do
  let kw ← expectKeyword "interface"
  discard (expectPunct "{")
  let mut methods := #[]
  while !(← peek).isPunct "}" do
    let t ← peek
    if !(t.kind matches .ident _) then unexpected t "a method name"
    if (← peekAt 1).isPunct "(" then
      let (name, nameSpan) ← readIdent
      let sig ← parseSignatureType (← peek).span.start
      methods := methods.push (.mk ⟨nameSpan.start, sig.span.stop⟩ [name] sig none)
    else
      let ty ← parseType
      methods := methods.push (.mk ty.span [] ty none)
    expectSemi
  discard (expectPunct "}")
  return .interfaceType ⟨kw.span.start, (← get).lastStop⟩ methods.toList

/-- Parameters and results, after `func` or a method name. The span starts at
`start`. -/
partial def parseSignatureType (start : Pos) : ParseM Expr := do
  let params ← parseParams
  let results ← parseResults
  return .funcType ⟨start, (← get).lastStop⟩ params results

partial def parseParamType : ParseM Expr := do
  let t ← peek
  if t.isPunct "..." then
    discard advance
    let elem ← parseType
    return .ellipsis ⟨t.span.start, elem.span.stop⟩ elem
  parseType

partial def parseParams : ParseM (List Field) := do
  discard (expectPunct "(")
  let mut items : Array (Expr × Option Expr) := #[]
  while !(← peek).isPunct ")" do
    let first ← nested parseParamType
    let next ← peek
    if next.isPunct "," || next.isPunct ")" then
      items := items.push (first, none)
    else
      items := items.push (first, some (← nested parseParamType))
    if (← peek).isPunct "," then discard advance
    else if !(← peek).isPunct ")" then unexpected (← peek) "',' or ')'"
  discard (expectPunct ")")
  groupParams items

partial def parseResults : ParseM (Option (List Field)) := do
  let t ← peek
  if t.isPunct "(" then return some (← parseParams)
  if t.isPunct "{" || t.isSemi || t.isEof then return none
  if startsType t then
    let ty ← parseType
    return some [.mk ty.span [] ty none]
  return none

-- Expressions

partial def parseExpr : ParseM Expr := parseBinary 1

partial def parseBinary (minPrec : Nat) : ParseM Expr := do
  let mut lhs ← parseUnary
  repeat
    let t ← peek
    match binaryPrec t with
    | some prec =>
      if prec < minPrec then break
      let op ← advance
      let rhs ← parseBinary (prec + 1)
      match op.kind with
      | .punct symbol => lhs := .binary ⟨lhs.span.start, rhs.span.stop⟩ symbol lhs rhs
      | _ => unreachable!
    | none => break
  return lhs

partial def parseUnary : ParseM Expr := do
  let t ← peek
  match t.kind with
  | .punct "<-" => failAt t "channels are not supported"
  | .punct "*" =>
    discard advance
    let arg ← parseUnary
    return .star ⟨t.span.start, arg.span.stop⟩ arg
  | .punct "+" | .punct "-" | .punct "!" | .punct "^" | .punct "&" =>
    discard advance
    let arg ← parseUnary
    match t.kind with
    | .punct op => return .unary ⟨t.span.start, arg.span.stop⟩ op arg
    | _ => unreachable!
  | _ => parsePrimary

partial def parseOperand : ParseM Expr := do
  let t ← peek
  refuseKeyword t
  match t.kind with
  | .ident name =>
    discard advance
    return .ident t.span name
  | .lit kind raw =>
    discard advance
    return .lit t.span kind raw
  | .punct "(" =>
    discard advance
    let inner ← nested parseExpr
    discard (expectPunct ")")
    return .paren ⟨t.span.start, (← get).lastStop⟩ inner
  | .punct "[" | .keyword "map" | .keyword "struct" | .keyword "interface" => parseType
  | .keyword "func" =>
    discard advance
    let type ← parseSignatureType t.span.start
    if !(← peek).isPunct "{" then return type
    let body ← nested parseBlock
    return .funcLit ⟨t.span.start, body.span.stop⟩ type body
  | _ => unexpected t "an expression"

partial def parseElement : ParseM Expr := do
  let key ← if (← peek).isPunct "{" then parseLiteralValue none else parseExpr
  if (← peek).isPunct ":" then
    discard advance
    let value ← if (← peek).isPunct "{" then parseLiteralValue none else parseExpr
    return .keyValue ⟨key.span.start, value.span.stop⟩ key value
  return key

/-- `{…}` after an optional type. -/
partial def parseLiteralValue (type : Option Expr) : ParseM Expr := do
  let lb ← expectPunct "{"
  let elts ← nested do
    let mut elts := #[]
    while !(← peek).isPunct "}" do
      elts := elts.push (← parseElement)
      if (← peek).isPunct "," then discard advance
      else if !(← peek).isPunct "}" then unexpected (← peek) "',' or '}'"
    return elts
  discard (expectPunct "}")
  let start := (type.map (·.span.start)).getD lb.span.start
  return .composite ⟨start, (← get).lastStop⟩ type elts.toList

partial def parseArgs : ParseM (List Expr × Bool) := nested do
  let mut args := #[]
  let mut ellipsis := false
  while !(← peek).isPunct ")" do
    args := args.push (← parseExpr)
    if (← peek).isPunct "..." then
      discard advance
      ellipsis := true
    if (← peek).isPunct "," then discard advance
    else if !(← peek).isPunct ")" then unexpected (← peek) "',' or ')'"
  return (args.toList, ellipsis)

partial def parsePrimary : ParseM Expr := do
  let mut x ← parseOperand
  repeat
    let t ← peek
    if t.isPunct "." then
      discard advance
      if (← peek).isPunct "(" then
        discard advance
        let type ← nested do
          if (← peek).isKeyword "type" then
            discard advance
            pure none
          else some <$> parseType
        discard (expectPunct ")")
        x := .typeAssert ⟨x.span.start, (← get).lastStop⟩ x type
        continue
      let (name, span) ← readIdent
      x := .selector ⟨x.span.start, span.stop⟩ x name
    else if t.isPunct "[" then
      discard advance
      let (low, isSlice, high) ← nested do
        let low ← if (← peek).isPunct ":" then pure none else some <$> parseExpr
        if (← peek).isPunct ":" then
          discard advance
          if (← peek).isPunct "]" then return (low, true, none)
          let high ← parseExpr
          if (← peek).isPunct ":" then failAt (← peek) "three-index slices are not supported"
          return (low, true, some high)
        return (low, false, none)
      discard (expectPunct "]")
      let span : Span := ⟨x.span.start, (← get).lastStop⟩
      if isSlice then x := .sliceExpr span x low high
      else
        match low with
        | some idx => x := .index span x idx
        | none => unexpected t "an index"
    else if t.isPunct "(" then
      discard advance
      let (args, ellipsis) ← parseArgs
      discard (expectPunct ")")
      x := .call ⟨x.span.start, (← get).lastStop⟩ x args ellipsis
    else if t.isPunct "{" && isLiteralType x && ((← get).exprLev ≥ 0 || !isTypeName x) then
      x ← parseLiteralValue (some x)
    else break
  return x

partial def parseExprList : ParseM (List Expr) := do
  let mut list := #[← parseExpr]
  while (← peek).isPunct "," do
    discard advance
    list := list.push (← parseExpr)
  return list.toList

-- Declarations

partial def parseSpec (keyword : String) : ParseM Spec := do
  match keyword with
  | "import" =>
    let t ← peek
    let name ← match t.kind with
      | .ident n => discard advance; pure (some n)
      | _ => pure none
    let pathTok ← advance
    match pathTok.kind with
    | .lit .string raw => return .import ⟨t.span.start, pathTok.span.stop⟩ raw name
    | _ => unexpected pathTok "an import path"
  | "type" =>
    let (name, span) ← readIdent
    -- `[T any]` or `[T, U any]` declares type parameters; `[16]` and `[N]`
    -- are array lengths.
    if (← peek).isPunct "[" && ((← peekAt 1).kind matches .ident _) &&
        !((← peekAt 2).isPunct "]") then
      failAt (← peek) "type parameters are not supported"
    let alias := (← peek).isPunct "="
    if alias then discard advance
    let ty ← parseType
    return .type ⟨span.start, ty.span.stop⟩ name ty alias
  | _ =>
    let (first, firstSpan) ← readIdent
    let mut names := #[first]
    let mut stop := firstSpan.stop
    while (← peek).isPunct "," do
      discard advance
      let (n, s) ← readIdent
      names := names.push n
      stop := s.stop
    let t ← peek
    let ty ← if t.isPunct "=" || t.isSemi || t.isPunct ")" then pure none else some <$> parseType
    if let some ty := ty then stop := ty.span.stop
    let values ← if (← peek).isPunct "=" then
        discard advance
        parseExprList
      else pure []
    if let some v := values.getLast? then stop := v.span.stop
    return .value ⟨firstSpan.start, stop⟩ names.toList ty values

partial def parseGenDecl : ParseM GenDecl := do
  let kw ← advance
  let keyword ← match kw.kind with
    | .keyword w => pure w
    | _ => unexpected kw "a declaration"
  if (← peek).isPunct "(" then
    discard advance
    let mut specs := #[]
    while !(← peek).isPunct ")" do
      specs := specs.push (← parseSpec keyword)
      expectSemi
    discard (expectPunct ")")
    return .mk ⟨kw.span.start, (← get).lastStop⟩ keyword specs.toList
  let spec ← parseSpec keyword
  let stop := match spec with
    | .import s .. | .type s .. | .value s .. => s.stop
  return .mk ⟨kw.span.start, stop⟩ keyword [spec]

-- Statements

partial def parseSimple (allowRange : Bool) : ParseM Simple := do
  let lhs ← parseExprList
  let t ← peek
  match t.kind with
  | .punct op =>
    if assignOps.contains op then
      discard advance
      if allowRange && (op == "=" || op == ":=") && (← peek).isKeyword "range" then
        discard advance
        return .range op lhs (← parseExpr)
      let rhs ← parseExprList
      return .stmt (.assign ⟨lhs.head!.span.start, rhs.getLast!.span.stop⟩ op lhs rhs)
    if op == "++" || op == "--" then
      discard advance
      match lhs with
      | [x] => return .stmt (.incDec ⟨x.span.start, t.span.stop⟩ op x)
      | _ => failAt t s!"'{op}' takes one operand"
    if op == ":" then failAt t "labels are not supported"
  | _ => pure ()
  match lhs with
  | [x] => return .stmt (.expr x.span x)
  | _ => unexpected t "':=' or '='"

partial def simpleStmt (allowRange : Bool := false) : ParseM Stmt := do
  match ← parseSimple allowRange with
  | .stmt s => return s
  | .range .. => failAt (← peek) "unexpected 'range'"

partial def exprOf (s : Stmt) (t : Token) : ParseM Expr :=
  match s with
  | .expr _ e => pure e
  | _ => failAt t "expected an expression"

partial def parseBlock : ParseM Stmt := do
  let lb ← expectPunct "{"
  let body ← withExprLev 0 parseStmtList
  discard (expectPunct "}")
  return .block ⟨lb.span.start, (← get).lastStop⟩ body

partial def parseStmtList : ParseM (List Stmt) := do
  let mut body := #[]
  repeat
    let t ← peek
    if t.isPunct "}" || t.isKeyword "case" || t.isKeyword "default" || t.isEof then break
    if t.isSemi then failAt t "empty statements are not supported"
    body := body.push (← parseStmt)
    expectSemi
  return body.toList

partial def parseStmt : ParseM Stmt := do
  let t ← peek
  refuseKeyword t
  match t.kind with
  | .punct "{" => parseBlock
  | .keyword "if" => parseIf
  | .keyword "for" => parseFor
  | .keyword "switch" => parseSwitch
  | .keyword "return" =>
    discard advance
    let next ← peek
    if next.isSemi || next.isPunct "}" then return .ret t.span []
    let results ← parseExprList
    return .ret ⟨t.span.start, results.getLast!.span.stop⟩ results
  | .keyword "break" | .keyword "continue" =>
    discard advance
    if (← peek).kind matches .ident _ then failAt (← peek) "labels are not supported"
    return if t.isKeyword "break" then .brk t.span else .cont t.span
  | .keyword "var" | .keyword "const" | .keyword "type" =>
    let d ← parseGenDecl
    return .decl d.span d
  | .keyword "defer" =>
    discard advance
    let call ← parseExpr
    if !(call matches .call ..) then failAt t "'defer' needs a function call"
    return .deferStmt ⟨t.span.start, call.span.stop⟩ call
  | _ => simpleStmt

partial def parseIf : ParseM Stmt := do
  let kw ← expectKeyword "if"
  let (init, cond) ← withExprLev (-1) do
    let first ← simpleStmt
    if (← peek).isPunct ";" then
      discard advance
      return (some first, ← parseExpr)
    return (none, ← exprOf first kw)
  let body ← parseBlock
  let els ← if (← peek).isKeyword "else" then
      discard advance
      if (← peek).isKeyword "if" then some <$> parseIf
      else some <$> parseBlock
    else pure none
  let stop := ((els.map Stmt.span).getD body.span).stop
  return .ifStmt ⟨kw.span.start, stop⟩ init cond body els

partial def parseFor : ParseM Stmt := do
  let kw ← expectKeyword "for"
  let head ← withExprLev (-1) do
    let t ← peek
    if t.isPunct "{" then return Sum.inl (none, none, none)
    if t.isKeyword "range" then
      discard advance
      return Sum.inr (none, [], ← parseExpr)
    let first ← if t.isPunct ";" then pure none else some <$> parseSimple true
    match first with
    | some (.range op lhs x) => return Sum.inr (some op, lhs, x)
    | _ => pure ()
    let firstStmt := match first with
      | some (.stmt s) => some s
      | _ => none
    if !(← peek).isPunct ";" then
      match firstStmt with
      | some s => return Sum.inl (none, some (← exprOf s t), none)
      | none => unexpected (← peek) "a condition"
    discard advance
    let cond ← if (← peek).isPunct ";" then pure none else some <$> parseExpr
    discard (expectPunct ";")
    let post ← if (← peek).isPunct "{" then pure none else some <$> simpleStmt
    return Sum.inl (firstStmt, cond, post)
  let body ← parseBlock
  let span : Span := ⟨kw.span.start, body.span.stop⟩
  match head with
  | .inl (init, cond, post) => return .forStmt span init cond post body
  | .inr (op, lhs, x) =>
    match lhs with
    | [] => return .range span op none none x body
    | [k] => return .range span op (some k) none x body
    | [k, v] => return .range span op (some k) (some v) x body
    | _ => failAt kw "a range clause takes at most two variables"

partial def parseCaseClause : ParseM CaseClause := do
  let t ← advance
  let exprs ← if t.isKeyword "case" then some <$> parseExprList
    else if t.isKeyword "default" then pure none
    else unexpected t "'case' or 'default'"
  discard (expectPunct ":")
  let colonStop := (← get).lastStop
  let body ← parseStmtList
  let stop := ((body.getLast?.map Stmt.span).map (·.stop)).getD colonStop
  return .mk ⟨t.span.start, stop⟩ exprs body

partial def parseSwitch : ParseM Stmt := do
  let kw ← expectKeyword "switch"
  let (init, tagStmt) ← withExprLev (-1) do
    if (← peek).isPunct "{" then return (none, none)
    let first ← simpleStmt
    if (← peek).isPunct ";" then
      discard advance
      if (← peek).isPunct "{" then return (some first, none)
      return (some first, some (← simpleStmt))
    return (none, some first)
  let isTypeGuard : Stmt → Bool
    | .expr _ (.typeAssert _ _ none) => true
    | .assign _ ":=" [_] [.typeAssert _ _ none] => true
    | _ => false
  let guard? := tagStmt.filter isTypeGuard
  let tag ← match tagStmt, guard? with
    | some s, none => some <$> exprOf s kw
    | _, _ => pure none
  let lb ← expectPunct "{"
  let clauses ← withExprLev 0 do
    let mut clauses := #[]
    while !(← peek).isPunct "}" do
      clauses := clauses.push (← parseCaseClause)
    return clauses
  discard (expectPunct "}")
  let bodySpan : Span := ⟨lb.span.start, (← get).lastStop⟩
  if let some guard := guard? then
    return .typeSwitch ⟨kw.span.start, bodySpan.stop⟩ init guard bodySpan clauses.toList
  return .switchStmt ⟨kw.span.start, bodySpan.stop⟩ init tag bodySpan clauses.toList

end

def parseFuncDecl : ParseM Decl := do
  let kw ← expectKeyword "func"
  let recv ← if (← peek).isPunct "(" then some <$> parseParams else pure none
  let (name, _) ← readIdent
  if (← peek).isPunct "[" then failAt (← peek) "type parameters are not supported"
  let params ← parseParams
  let results ← parseResults
  if !(← peek).isPunct "{" then failAt (← peek) "a function without a body is not supported"
  let body ← parseBlock
  return .func ⟨kw.span.start, body.span.stop⟩ recv name params results body

def parseFile : ParseM File := do
  discard (expectKeyword "package")
  let (package, _) ← readIdent
  expectSemi
  let mut decls := #[]
  repeat
    let t ← peek
    if t.isEof then break
    match t.kind with
    | .keyword "func" => decls := decls.push (← parseFuncDecl)
    | .keyword "import" | .keyword "var" | .keyword "const" | .keyword "type" =>
      decls := decls.push (.gen (← parseGenDecl))
    | _ => unexpected t "a declaration"
    let t ← peek
    if t.isSemi then discard advance
    else if !t.isEof then unexpected t "';' or a line break"
  return { package, decls := decls.toList }

end Parse

/-- The syntax tree of a Go source file. -/
def parse (source : String) : Except ParseError File := do
  let tokens ← lex source
  match Parse.parseFile.run { tokens } with
  | .ok f _ => .ok f
  | .error e _ => .error e

end tolean.Go.Syntax
