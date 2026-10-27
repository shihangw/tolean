import tolean.TypeScript.Syntax.Ast
import tolean.TypeScript.Syntax.Lexer
import tolean.TypeScript.Syntax.Equality

/-!
The TypeScript parser: recursive descent, with precedence climbing for binary
operators and automatic semicolon insertion as in ECMAScript §12.10.

It reads a part of TypeScript and refuses everything else with a position and
a reason. Where `tsc` and JavaScript could read the same tokens two ways, it
refuses the code instead of choosing one:

- `f < A, B > (x)`: `tsc` reads type arguments, JavaScript reads comparisons.
  The parser refuses a `<` operator that a `>` follows before the end of its
  group or statement.
- `(a)` or `async(a)`, then `{`: `tsc` reads an arrow function that lacks its
  `=>`, JavaScript reads `(a); {`. The parser refuses the `{` there, and a
  `:` after `async(a)`, which `tsc` reads as a return type.
- `a ?? b || c` without parentheses is a syntax error, and so is `-a ** b`.
- Declarations stand only where JavaScript allows them, `return` only in a
  function, `break` and `continue` only in a loop.
-/
namespace tolean.TypeScript.Syntax

open tolean

structure ParseState where
  /-- The tokens that are left to read. The parser reads them from the front,
  so the kernel runs it in time linear in the tokens, as it does a list. The
  last token, `eof`, stays. -/
  rest : List Token
  /-- The number of tokens in `rest`. -/
  left : Nat
  /-- The last token of the file. -/
  eof : Token
  /-- The end of the last token read: the end of the node being read. -/
  lastStop : Pos := ⟨1, 1⟩
  inFunction : Bool := false
  loopDepth : Nat := 0
  /-- Syntax newer than the target is refused. -/
  target : Edition := .default

abbrev ParseM := EStateM ParseError ParseState

namespace Parse

/-- Names that strict-mode code may not bind or read as plain variables, and
`eval` and `arguments`, which are not plain variables. -/
def refusedNames : List String :=
  ["implements", "interface", "let", "package", "private", "protected", "public",
   "static", "yield", "await", "eval", "arguments"]

def keywordTypes : List String :=
  ["any", "unknown", "number", "bigint", "boolean", "string", "symbol", "object",
   "never", "undefined"]

/-- Words that start a type operator or predicate in `tsc`, not a type name. -/
def typeOperatorWords : List String := ["keyof", "unique", "readonly", "infer", "asserts", "is"]

def peekAt (k : Nat) : ParseM Token := do
  let s ← get
  return s.rest[k]?.getD s.eof

def peek : ParseM Token := peekAt 0

def advance : ParseM Token := do
  let s ← get
  let t := s.rest.headD s.eof
  let s := match s.rest with
    | _ :: rest@(_ :: _) => { s with rest, left := s.left - 1 }
    | _ => s
  set { s with lastStop := t.span.stop }
  return t

def skip (count : Nat) : ParseM Unit := do
  for _ in [0:count] do discard advance

def spanFrom (start : Pos) : ParseM Span := do
  return ⟨start, (← get).lastStop⟩

def failAt {A : Type} (t : Token) (message : String) : ParseM A :=
  throw ({ span := t.span, message } : ParseError)

/-- Fuel for the calls that start here, and for a loop: ten units for each
token left, and ten more. A loop reads at least one token in each step, and a
call nests at most a few calls deeper for each token it reads, so the parser
never uses up its fuel. With fuel, every function of the parser is total, and
the kernel can run it. -/
def budget : ParseM Nat := do
  return 10 * ((← get).left + 1)

/-- The parser used up its fuel, which `budget` rules out. -/
def outOfFuel {A : Type} : ParseM A := do
  failAt (← peek) "the parser ran out of fuel"

/-- Run `step` from `state` until it says to stop, and give the last state.
It is the parser's `repeat`, which the kernel cannot run. -/
def iterate {σ : Type} (fuel : Nat) (state : σ) (step : σ → ParseM (σ × Bool)) : ParseM σ := do
  let fuel + 1 := fuel | outOfFuel
  let (state, again) ← step state
  if again then iterate fuel state step else return state

/-- Refuse `t` unless the target edition has `f`. -/
def requireFeature (t : Token) (f : Feature) : ParseM Unit := do
  let target := (← get).target
  unless target.supports f do failAt t (f.refusal target)

def unexpected {A : Type} (t : Token) (wanted : String) : ParseM A :=
  failAt t s!"expected {wanted}, found {t.kind.describe}"

def expectPunct (symbol : String) : ParseM Token := do
  let t ← peek
  if t.isPunct symbol then advance else unexpected t s!"'{symbol}'"

/-- A name that a declaration binds, or that an expression reads. -/
def readName : ParseM String := do
  let t ← advance
  match t.kind with
  | .ident name =>
    if refusedNames.contains name then failAt t s!"'{name}' is not supported as a name"
    return name
  | _ => unexpected t "a name"

/-- A property name after `.`, or a field name: any identifier or keyword. -/
def readPropertyName : ParseM String := do
  let t ← advance
  match t.kind with
  | .ident name | .keyword name => return name
  | _ => unexpected t "a property name"

/-- End a statement: read its `;`, or insert one where ECMAScript inserts it,
before a line break, a `}` or the end of the file. -/
def endStatement : ParseM Unit := do
  let t ← peek
  if t.isPunct ";" then discard advance
  else if t.isPunct "}" || t.isEof || t.newlineBefore then return
  else unexpected t "';'"

def withLoop {A : Type} (body : ParseM A) : ParseM A := do
  modify fun s => { s with loopDepth := s.loopDepth + 1 }
  let result ← body
  modify fun s => { s with loopDepth := s.loopDepth - 1 }
  return result

/-! ### Types -/

mutual

def parseType (fuel : Nat) : ParseM TypeExpr := do
  let fuel + 1 := fuel | outOfFuel
  let t ← peek
  let start := t.span.start
  -- `type A = | B` is a union of one member in `tsc`.
  let leading := t.isPunct "|"
  if leading then discard advance
  let first ← parseArrayType fuel
  let members ← iterate (← budget) #[first] fun members => do
    let t ← peek
    if !t.isPunct "|" then return (members, false)
    discard advance
    return (members.push (← parseArrayType fuel), true)
  let t ← peek
  if t.isPunct "&" then failAt t "intersection types are not supported"
  if leading || members.size > 1 then return .union (← spanFrom start) members.toList
  return first

def parseArrayType (fuel : Nat) : ParseM TypeExpr := do
  let fuel + 1 := fuel | outOfFuel
  let start := (← peek).span.start
  iterate (← budget) (← parsePrimaryType fuel) fun type => do
    let t ← peek
    -- `tsc` does not read `T` `[]` across a line break as an array type.
    if !t.isPunct "[" || t.newlineBefore then return (type, false)
    unless (← peekAt 1).isPunct "]" do failAt t "indexed access types are not supported"
    skip 2
    return (.array (← spanFrom start) type, true)

def parsePrimaryType (fuel : Nat) : ParseM TypeExpr := do
  let fuel + 1 := fuel | outOfFuel
  let t ← advance
  match t.kind with
  | .ident name =>
    let next ← peek
    if next.isPunct "." then failAt next "qualified type names are not supported"
    if keywordTypes.contains name then return .keyword t.span name
    if typeOperatorWords.contains name then failAt t s!"'{name}' types are not supported"
    if refusedNames.contains name then failAt t s!"'{name}' is not supported as a name"
    if !next.isPunct "<" || next.newlineBefore then return .ref t.span name []
    discard advance
    let args ← iterate (← budget) #[] fun args => do
      let args := args.push (← parseType fuel)
      let t ← peek
      if !t.isPunct "," then return (args, false)
      discard advance
      return (args, true)
    let _ ← expectPunct ">"
    return .ref (← spanFrom t.span.start) name args.toList
  | .keyword "void" => return .keyword t.span "void"
  | .keyword "null" => return .null t.span
  | .keyword "true" => return .literal t.span (.bool true)
  | .keyword "false" => return .literal t.span (.bool false)
  | .string value => return .literal t.span (.string value)
  | .number text => return .literal t.span (.number text)
  | .bigint text => return .literal t.span (.bigint text)
  | .punct "(" =>
    let inner ← parseType fuel
    let _ ← expectPunct ")"
    return .paren (← spanFrom t.span.start) inner
  | _ => unexpected t "a type"

end

/-! ### Expressions -/

/-- `>` tokens that touch make one operator: `>=`, `>>`, `>>>`, `>>=`, `>>>=`.
Gives the operator and its number of tokens. -/
def peekGreater : ParseM (String × Nat) := do
  let t0 ← peekAt 0
  let t1 ← peekAt 1
  let t2 ← peekAt 2
  let t3 ← peekAt 3
  let touches (a b : Token) : Bool := b.span.start == a.span.stop
  if t1.isPunct ">" && touches t0 t1 then
    if t2.isPunct ">" && touches t1 t2 then
      if t3.isPunct "=" && touches t2 t3 then return (">>>=", 4)
      return (">>>", 3)
    if t2.isPunct "=" && touches t1 t2 then return (">>=", 3)
    return (">>", 2)
  if t1.isPunct "=" && touches t0 t1 then return (">=", 2)
  return (">", 1)

def peekBinaryOp : ParseM (Option (BinOp × Nat)) := do
  let t ← peek
  match t.kind with
  | .keyword "in" => return some (.«in», 1)
  | .keyword "instanceof" => return some (.instanceof, 1)
  | .punct ">" =>
    let (symbol, width) ← peekGreater
    return (BinOp.ofSymbol? symbol).map (·, width)
  | .punct symbol => return (BinOp.ofSymbol? symbol).map (·, 1)
  | _ => return none

def peekAssignOp : ParseM (Option (AssignOp × Nat)) := do
  let t ← peek
  match t.kind with
  | .punct ">" =>
    let (symbol, width) ← peekGreater
    return (AssignOp.ofSymbol? symbol).map (·, width)
  | .punct symbol => return (AssignOp.ofSymbol? symbol).map (·, 1)
  | _ => return none

/-- `tsc` reads `f < A, B > (x)` as a call with type arguments, where
JavaScript reads two comparisons, and type stripping keeps `tsc`'s reading.
Tolean does not parse type arguments in expressions, so it refuses every `<`
operator that `tsc` could read as their start: any `<` followed by a `>`
before the end of its group or statement. This refuses some plain
comparisons, such as `a < b && c > d`; parentheses make them parse. -/
def refuseTypeArgumentLookalike (lt : Token) : ParseM Unit := do
  let s ← get
  let mut depth := 0
  for t in s.rest.drop 1 do
    match t.kind with
    | .eof => return
    | .punct "(" | .punct "[" | .punct "{" => depth := depth + 1
    | .punct ")" | .punct "]" | .punct "}" =>
      if depth == 0 then return
      depth := depth - 1
    | .punct ";" => if depth == 0 then return
    | .punct ">" =>
      failAt lt ("tsc may read this '<' as the start of type arguments; " ++
        "add parentheses around the comparison")
    | _ => pure ()

/-- `tsc` reads `(a)` or `async(a)` followed by `{` as an arrow function that
lacks its `=>`, even across a line break, and reports an error. JavaScript
reads `(a); {`. Call after the `)`. -/
def refuseArrowLookalike : ParseM Unit := do
  let t ← peek
  if t.isPunct "{" then
    failAt t "tsc may read this '(…) {' as an arrow function; end the statement with ';'"

/-- `tsc` also reads `async()` or `async(a)` followed by `:`, as in
`c ? async() : d`, as an arrow function with a return type. JavaScript reads
a call of a function named `async`. Call after the `)`. -/
def refuseAsyncArrowLookalike : ParseM Unit := do
  refuseArrowLookalike
  let t ← peek
  if t.isPunct ":" then
    failAt t "tsc may read this 'async(…) :' as an arrow function; put the call in parentheses"

def unaryOp? (t : Token) : Option UnaryOp :=
  match t.kind with
  | .punct "!" => some .not
  | .punct "-" => some .neg
  | .punct "+" => some .plus
  | .punct "~" => some .bitNot
  | .keyword "typeof" => some .typeof
  | .keyword "void" => some .void
  | _ => none

def updateOp? (t : Token) : Option UpdateOp :=
  if t.isPunct "++" then some .increment
  else if t.isPunct "--" then some .decrement
  else none

mutual

/-- An expression where a `,` would be the comma operator. -/
def parseExpression (fuel : Nat) : ParseM Expr := do
  let fuel + 1 := fuel | outOfFuel
  let expr ← parseAssign fuel
  let t ← peek
  if t.isPunct "," then failAt t "the comma operator is not supported"
  return expr

def parseAssign (fuel : Nat) : ParseM Expr := do
  let fuel + 1 := fuel | outOfFuel
  let start := (← peek).span.start
  let lhs ← parseConditional fuel
  let t ← peek
  if t.isPunct "=>" then failAt t "arrow functions are not supported"
  let some (op, width) ← peekAssignOp | return lhs
  unless lhs.isSimpleTarget do failAt t "only a name, a property or an element can be assigned"
  match op with
  | .exp => requireFeature t .exponent
  | .and | .or | .coalesce => requireFeature t .logicalAssignment
  | _ => pure ()
  skip width
  let value ← parseAssign fuel
  return .assign (← spanFrom start) op lhs value

def parseConditional (fuel : Nat) : ParseM Expr := do
  let fuel + 1 := fuel | outOfFuel
  let start := (← peek).span.start
  let test ← parseBinary fuel 0
  if !(← peek).isPunct "?" then return test
  discard advance
  let ifTrue ← parseAssign fuel
  let _ ← expectPunct ":"
  let ifFalse ← parseAssign fuel
  return .cond (← spanFrom start) test ifTrue ifFalse

def parseBinary (fuel : Nat) (minPrec : Nat) : ParseM Expr := do
  let fuel + 1 := fuel | outOfFuel
  let start := (← peek).span.start
  iterate (← budget) (← parseUnary fuel) fun lhs => do
    let some (op, width) ← peekBinaryOp | return (lhs, false)
    if op.precedence < minPrec then return (lhs, false)
    let opToken ← peek
    if op == .exp && (lhs matches .unary ..) then
      failAt opToken "put parentheses around a unary operand of '**'"
    if op == .lt || op == .shl then refuseTypeArgumentLookalike opToken
    if op == .exp then requireFeature opToken .exponent
    if op == .coalesce then requireFeature opToken .nullishCoalescing
    skip width
    -- `**` is right-associative.
    let rhs ← parseBinary fuel (if op == .exp then op.precedence else op.precedence + 1)
    if (op == .coalesce && (lhs.isLogical || rhs.isLogical)) ||
        ((op == .and || op == .or) && (lhs.isCoalesce || rhs.isCoalesce)) then
      failAt opToken "'??' cannot be mixed with '&&' or '||' without parentheses"
    return (.binary (← spanFrom start) op lhs rhs, true)

def parseUnary (fuel : Nat) : ParseM Expr := do
  let fuel + 1 := fuel | outOfFuel
  let t ← peek
  if let some op := unaryOp? t then
    discard advance
    let arg ← parseUnary fuel
    return .unary (← spanFrom t.span.start) op arg
  if let some op := updateOp? t then
    discard advance
    let arg ← parseLeftHandSide fuel
    unless arg.isSimpleTarget do failAt t s!"'{op.symbol}' needs a name, a property or an element"
    return .prefix (← spanFrom t.span.start) op arg
  parsePostfix fuel

def parsePostfix (fuel : Nat) : ParseM Expr := do
  let fuel + 1 := fuel | outOfFuel
  let start := (← peek).span.start
  let arg ← parseLeftHandSide fuel
  let t ← peek
  -- No line break may come before a postfix `++` or `--`.
  let some op := updateOp? t | return arg
  if t.newlineBefore then return arg
  unless arg.isSimpleTarget do failAt t s!"'{op.symbol}' needs a name, a property or an element"
  discard advance
  return .postfix (← spanFrom start) op arg

def parseLeftHandSide (fuel : Nat) : ParseM Expr := do
  let fuel + 1 := fuel | outOfFuel
  let start := (← peek).span.start
  iterate (← budget) (← parsePrimary fuel) fun expr => do
    let t ← peek
    if t.isPunct "." then
      discard advance
      let name ← readPropertyName
      return (.member (← spanFrom start) expr name, true)
    else if t.isPunct "[" then
      discard advance
      let idx ← parseExpression fuel
      let _ ← expectPunct "]"
      return (.index (← spanFrom start) expr idx, true)
    else if t.isPunct "(" then
      let isAsync := (expr matches .ident _ "async") && !t.newlineBefore
      let args ← parseArguments fuel
      if isAsync then refuseAsyncArrowLookalike
      return (.call (← spanFrom start) expr args, true)
    else if t.isPunct "?." then failAt t "optional chaining is not supported"
    else if t.isPunct "!" && !t.newlineBefore then
      failAt t "non-null assertions are not supported"
    else return (expr, false)

def parseArguments (fuel : Nat) : ParseM (List Expr) := do
  let fuel + 1 := fuel | outOfFuel
  let _ ← expectPunct "("
  let args ← iterate (← budget) #[] fun args => do
    let t ← peek
    if t.isPunct ")" then return (args, false)
    if t.isPunct "..." then failAt t "spread arguments are not supported"
    let args := args.push (← parseAssign fuel)
    let t ← peek
    if t.isPunct "," then discard advance
    else if !t.isPunct ")" then unexpected t "',' or ')'"
    return (args, true)
  let _ ← expectPunct ")"
  return args.toList

def parseArrayLiteral (fuel : Nat) : ParseM Expr := do
  let fuel + 1 := fuel | outOfFuel
  let start := (← expectPunct "[").span.start
  let elems ← iterate (← budget) #[] fun elems => do
    let t ← peek
    if t.isPunct "]" then return (elems, false)
    if t.isPunct "," then failAt t "array holes are not supported"
    if t.isPunct "..." then failAt t "spread elements are not supported"
    let elems := elems.push (← parseAssign fuel)
    let t ← peek
    if t.isPunct "," then discard advance
    else if !t.isPunct "]" then unexpected t "',' or ']'"
    return (elems, true)
  let _ ← expectPunct "]"
  return .array (← spanFrom start) elems.toList

def parseProperty (fuel : Nat) : ParseM Property := do
  let fuel + 1 := fuel | outOfFuel
  let t ← advance
  let start := t.span.start
  let key : PropKey ← match t.kind with
    | .ident name | .keyword name => pure (.ident name)
    | .string value => pure (.string value)
    | .number text => pure (.number text)
    | .punct "[" => failAt t "computed property names are not supported"
    | .punct "..." => failAt t "spread properties are not supported"
    | _ => unexpected t "a property"
  let next ← peek
  if next.isPunct ":" then
    discard advance
    let value ← parseAssign fuel
    return .keyValue (← spanFrom start) key value
  if next.isPunct "," || next.isPunct "}" then
    let .ident name := t.kind | unexpected next "':'"
    if refusedNames.contains name then failAt t s!"'{name}' is not supported as a name"
    return .shorthand t.span name
  if next.isPunct "(" || next.isPunct "<" then failAt next "methods are not supported"
  unexpected next "':'"

def parseObjectLiteral (fuel : Nat) : ParseM Expr := do
  let fuel + 1 := fuel | outOfFuel
  let start := (← expectPunct "{").span.start
  let props ← iterate (← budget) #[] fun props => do
    let t ← peek
    if t.isPunct "}" then return (props, false)
    let props := props.push (← parseProperty fuel)
    let t ← peek
    if t.isPunct "," then discard advance
    else if !t.isPunct "}" then unexpected t "',' or '}'"
    return (props, true)
  let _ ← expectPunct "}"
  return .object (← spanFrom start) props.toList

def parsePrimary (fuel : Nat) : ParseM Expr := do
  let fuel + 1 := fuel | outOfFuel
  let t ← peek
  match t.kind with
  | .ident _ => return .ident t.span (← readName)
  | .number text =>
    discard advance
    return .number t.span text
  | .bigint text =>
    discard advance
    return .bigint t.span text
  | .string value =>
    discard advance
    return .string t.span value
  | .keyword "true" =>
    discard advance
    return .bool t.span true
  | .keyword "false" =>
    discard advance
    return .bool t.span false
  | .keyword "null" =>
    discard advance
    return .null t.span
  | .punct "(" =>
    discard advance
    let inner ← parseExpression fuel
    let _ ← expectPunct ")"
    refuseArrowLookalike
    return .paren (← spanFrom t.span.start) inner
  | .punct "[" => parseArrayLiteral fuel
  | .punct "{" => parseObjectLiteral fuel
  | .keyword word => failAt t s!"'{word}' is not supported in an expression"
  | _ => unexpected t "an expression"

end

/-! ### Statements -/

/-- `const` or `let`, through the end of the statement. -/
def parseVarDecl : ParseM VarDecl := do
  let keyword ← advance
  let kind := if keyword.isKeyword "const" then VarKind.const else .«let»
  let t ← peek
  if t.isPunct "[" || t.isPunct "{" then failAt t "destructuring is not supported"
  let name ← readName
  let mut type := none
  if (← peek).isPunct ":" then
    discard advance
    type := some (← parseType (← budget))
  let mut init := none
  if (← peek).isPunct "=" then
    discard advance
    init := some (← parseAssign (← budget))
  let t ← peek
  if t.isPunct "," then failAt t "declare one variable per statement"
  if kind == .const && init.isNone then failAt keyword "a 'const' needs a value"
  endStatement
  return { kind, name, type, init }

/-- Statements that JavaScript does not allow without a block around them, in
the body of `if`, `for` and `while`. -/
def refuseDeclaration (t : Token) : ParseM Unit := do
  if t.isKeyword "const" || t.isIdent "let" then
    failAt t "a declaration here needs a block around it"

mutual

def parseStatement (fuel : Nat) : ParseM Stmt := do
  let fuel + 1 := fuel | outOfFuel
  let t ← peek
  let start := t.span.start
  match t.kind with
  | .punct "{" => parseBlock fuel
  | .punct ";" =>
    discard advance
    return .empty t.span
  | .keyword "const" | .ident "let" =>
    let decl ← parseVarDecl
    return .varDecl (← spanFrom start) decl
  | .keyword "if" =>
    discard advance
    let _ ← expectPunct "("
    let test ← parseExpression (← budget)
    let _ ← expectPunct ")"
    let thenBranch ← parseBranch fuel
    let mut elseBranch := none
    if (← peek).isKeyword "else" then
      discard advance
      elseBranch := some (← parseBranch fuel)
    return .ifStmt (← spanFrom start) test thenBranch elseBranch
  | .keyword "for" => parseForOf fuel
  | .keyword "while" =>
    discard advance
    let _ ← expectPunct "("
    let test ← parseExpression (← budget)
    let _ ← expectPunct ")"
    let body ← withLoop (parseBranch fuel)
    return .whileStmt (← spanFrom start) test body
  | .keyword "return" =>
    discard advance
    unless (← get).inFunction do failAt t "'return' outside a function"
    let next ← peek
    let mut value := none
    if !(next.isPunct ";" || next.isPunct "}" || next.isEof || next.newlineBefore) then
      value := some (← parseExpression (← budget))
    endStatement
    return .returnStmt (← spanFrom start) value
  | .keyword "break" | .keyword "continue" =>
    discard advance
    if (← get).loopDepth == 0 then failAt t s!"{t.kind.describe} outside a loop"
    let next ← peek
    if next.isAnyIdent && !next.newlineBefore then failAt next "labels are not supported"
    endStatement
    let span ← spanFrom start
    return if t.isKeyword "break" then .breakStmt span else .continueStmt span
  | .keyword "true" | .keyword "false" | .keyword "null" | .keyword "typeof"
  | .keyword "void" => parseExpressionStatement fuel
  | .keyword word => failAt t s!"'{word}' is not supported here"
  | _ => parseExpressionStatement fuel

/-- The body of `if`, `else`, `for` or `while`. -/
def parseBranch (fuel : Nat) : ParseM Stmt := do
  let fuel + 1 := fuel | outOfFuel
  refuseDeclaration (← peek)
  parseStatement fuel

def parseExpressionStatement (fuel : Nat) : ParseM Stmt := do
  let _ + 1 := fuel | outOfFuel
  let start := (← peek).span.start
  let expr ← parseExpression (← budget)
  endStatement
  return .exprStmt (← spanFrom start) expr

def parseForOf (fuel : Nat) : ParseM Stmt := do
  let fuel + 1 := fuel | outOfFuel
  let start := (← advance).span.start
  let t ← peek
  if t.isIdent "await" then failAt t "'for await' is not supported"
  let _ ← expectPunct "("
  let keyword ← peek
  let kind ← if keyword.isKeyword "const" then pure VarKind.const
    else if keyword.isIdent "let" then pure VarKind.«let»
    else failAt keyword "tolean supports only 'for (const x of …)' and 'for (let x of …)'"
  discard advance
  let t ← peek
  if t.isPunct "[" || t.isPunct "{" then failAt t "destructuring is not supported"
  let name ← readName
  let t ← peek
  unless t.isIdent "of" do failAt t "tolean supports only 'for … of' loops"
  discard advance
  let iterable ← parseAssign (← budget)
  let _ ← expectPunct ")"
  let body ← withLoop (parseBranch fuel)
  return .forOfStmt (← spanFrom start) kind name iterable body

def parseBlock (fuel : Nat) : ParseM Stmt := do
  let fuel + 1 := fuel | outOfFuel
  let start := (← expectPunct "{").span.start
  let body ← iterate (← budget) #[] fun body => do
    let t ← peek
    if t.isPunct "}" then return (body, false)
    if t.isEof then unexpected t "'}'"
    return (body.push (← parseStatement fuel), true)
  let _ ← expectPunct "}"
  return .block (← spanFrom start) body.toList

end

/-! ### Declarations -/

def parseParam : ParseM Param := do
  let t ← peek
  if t.isPunct "..." then failAt t "rest parameters are not supported"
  if t.isPunct "[" || t.isPunct "{" then failAt t "destructuring is not supported"
  if t.isKeyword "this" then failAt t "'this' parameters are not supported"
  let name ← readName
  let next ← peek
  if next.isPunct "?" then failAt next "optional parameters are not supported"
  let mut type := none
  if next.isPunct ":" then
    discard advance
    type := some (← parseType (← budget))
  let next ← peek
  if next.isPunct "=" then failAt next "default values are not supported"
  return { span := ← spanFrom t.span.start, name, type }

def parseFunction (start : Pos) (exported : Bool) : ParseM Decl := do
  discard advance
  let t ← peek
  if t.isPunct "*" then failAt t "generators are not supported"
  let name ← readName
  let t ← peek
  if t.isPunct "<" then failAt t "generic functions are not supported"
  let _ ← expectPunct "("
  let params ← iterate (← budget) #[] fun params => do
    let t ← peek
    if t.isPunct ")" then return (params, false)
    let params := params.push (← parseParam)
    let t ← peek
    if t.isPunct "," then discard advance
    else if !t.isPunct ")" then unexpected t "',' or ')'"
    return (params, true)
  let _ ← expectPunct ")"
  let mut returnType := none
  if (← peek).isPunct ":" then
    discard advance
    returnType := some (← parseType (← budget))
  let t ← peek
  unless t.isPunct "{" do unexpected t "'{' (a function needs a body)"
  modify fun s => { s with inFunction := true }
  let body ← parseBlock (← budget)
  modify fun s => { s with inFunction := false }
  return .function (← spanFrom start) exported name params.toList returnType body

def parseField : ParseM Field := do
  let t ← peek
  let next ← peekAt 1
  -- `readonly` is a modifier only before a name on the same line.
  let readonly := t.isIdent "readonly" && !next.newlineBefore &&
    (next.isAnyIdent || (next.kind matches .keyword _ | .string _ | .number _))
  if readonly then discard advance
  let name ← readPropertyName
  let optional := (← peek).isPunct "?"
  if optional then discard advance
  let next ← peek
  if next.isPunct "(" || next.isPunct "<" then failAt next "method signatures are not supported"
  unless next.isPunct ":" do unexpected next "':' (a field needs a type)"
  discard advance
  let type ← parseType (← budget)
  let next ← peek
  if next.isPunct ";" || next.isPunct "," then discard advance
  else if !(next.isPunct "}" || next.newlineBefore) then unexpected next "';' or ','"
  return { span := ← spanFrom t.span.start, readonly, name, optional, type }

def parseInterface (start : Pos) (exported : Bool) : ParseM Decl := do
  discard advance
  let name ← readName
  let t ← peek
  if t.isPunct "<" then failAt t "generic interfaces are not supported"
  if t.isKeyword "extends" then failAt t "'extends' is not supported"
  let _ ← expectPunct "{"
  let fields ← iterate (← budget) #[] fun fields => do
    let t ← peek
    if t.isPunct "}" then return (fields, false)
    if t.isEof then unexpected t "'}'"
    return (fields.push (← parseField), true)
  let _ ← expectPunct "}"
  return .interface (← spanFrom start) exported name fields.toList

def parseTypeAlias (start : Pos) (exported : Bool) : ParseM Decl := do
  discard advance
  let name ← readName
  let t ← peek
  if t.isPunct "<" then failAt t "generic type aliases are not supported"
  let _ ← expectPunct "="
  let type ← parseType (← budget)
  endStatement
  return .typeAlias (← spanFrom start) exported name type

def parseDecl : ParseM Decl := do
  let first ← peek
  let start := first.span.start
  let exported := first.isKeyword "export"
  if exported then discard advance
  let t ← peek
  let next ← peekAt 1
  -- `interface` and `type` start a declaration only before a name on the same
  -- line, as in `tsc`.
  let nameFollows := next.isAnyIdent && !next.newlineBefore
  if t.isKeyword "function" then parseFunction start exported
  else if t.isIdent "interface" && nameFollows then parseInterface start exported
  else if t.isIdent "type" && nameFollows then parseTypeAlias start exported
  else if exported then
    unless t.isKeyword "const" || t.isIdent "let" do
      failAt t "tolean supports 'export' only of a function, an interface, a type or a variable"
    let decl ← parseVarDecl
    return .exportedVar (← spanFrom start) decl
  else return .stmt (← parseStatement (← budget))

def parseModule : ParseM Module := do
  let decls ← iterate (← budget) #[] fun decls => do
    if (← peek).isEof then return (decls, false)
    return (decls.push (← parseDecl), true)
  return { decls := decls.toList }

end Parse

/-- Parse the tokens of a TypeScript module, refusing syntax newer than
`target`. The last token is `eof`. -/
def parseTokens (tokens : List Token) (target : Edition := .default) : Except ParseError Module :=
  let eof := tokens.getLastD { kind := .eof, span := ⟨⟨1, 1⟩, ⟨1, 1⟩⟩, newlineBefore := false }
  match Parse.parseModule.run { rest := tokens, left := tokens.length, eof, target } with
  | .ok m _ => .ok m
  | .error e _ => .error e

/-- Parse the characters of a TypeScript module, refusing syntax newer than
`target`. The kernel runs this in time linear in the source. -/
def parseChars (chars : List Char) (target : Edition := .default) : Except ParseError Module := do
  parseTokens (← lexChars chars target).toList target

open Lean in
/-- `chars!"ab"` is `['a', 'b']`. Lean reads the string literal as its
characters when it elaborates the file.

A certificate writes its source this way, so that it reads as the source and
the kernel never reads a `String`. When the kernel reduces `String.toList` on
a string literal, it takes time quadratic in the length of the literal
(https://github.com/leanprover/lean4/issues/16012). The kernel encodes the
characters as UTF-8 bytes and decodes them again, and it reads an `Array` as
a list, so each step of that loop takes linear time. A 2.7 KB source did not
finish in five minutes. -/
macro "chars!" s:str : term => do
  let cs : Array (TSyntax `term) := s.getString.toList.toArray.map fun c => ⟨Syntax.mkCharLit c⟩
  `(([$cs,*] : List Char))

/-- The characters of `lines`, with a line break between two lines. -/
def joinLines : List (List Char) → List Char
  | [] => []
  | [line] => line
  | line :: rest => line ++ '\n' :: joinLines rest

/-- The parser gives `m` for the characters `chars`. The kernel can decide this,
and a certificate does, with `parseChars_eq_of_parsesTo`. -/
def parsesTo (chars : List Char) (target : Edition) (m : Module) : Bool :=
  match parseChars chars target with
  | .ok m' => Module.beq m' m
  | .error _ => false

theorem parseChars_eq_of_parsesTo {chars : List Char} {target : Edition} {m : Module}
    (h : parsesTo chars target m = true) : parseChars chars target = .ok m := by
  unfold parsesTo at h
  split at h
  · next m' hm => rw [hm, (Module.beq_iff m' m).mp h]
  · simp at h

/-- Parse a TypeScript module, refusing syntax newer than `target`. -/
def parse (source : String) (target : Edition := .default) : Except ParseError Module :=
  parseChars source.toList target

end tolean.TypeScript.Syntax
