import tolean.TypeScript.Syntax.Parser

/-!
A syntax tree as TypeScript source, for the round trip of step 4 of the
certificates plan: the parser reads the printed source as the same tree.

The printer writes one form for each node, so that the proof of the round
trip follows the tree:

- Every statement and every declaration has a line of its own, and every
  statement ends in `;`. So no `;` is inserted, and no rule about a line break
  inside a statement applies.
- Two tokens are always one space apart. So no two tokens run together, and a
  `>=` or a `>>`, which the parser reads as `>` tokens that touch, is printed
  as one word.
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

def LitType.source : LitType → String
  | .string value => quote value
  | .number text | .bigint text => text
  | .bool b => if b then "true" else "false"

mutual

def TypeExpr.source : TypeExpr → String
  | .keyword _ name => name
  | .null _ => "null"
  | .literal _ lit => lit.source
  | .ref _ name [] => name
  | .ref _ name args => s!"{name} < {", ".intercalate (TypeExpr.sources args)} >"
  | .array _ elem => s!"{elem.source} [ ]"
  -- A union of one member is `| T`, as `type A = | T` writes it.
  | .union _ [member] => s!"| {member.source}"
  | .union _ members => " | ".intercalate (TypeExpr.sources members)
  | .paren _ inner => s!"( {inner.source} )"

def TypeExpr.sources : List TypeExpr → List String
  | [] => []
  | t :: ts => t.source :: TypeExpr.sources ts

end

def PropKey.source : PropKey → String
  | .ident name => name
  | .string value => quote value
  | .number text => text

/-- `items` between `open` and `close`, with `, ` between two of them. -/
def enclose (open_ close : String) : List String → String
  | [] => s!"{open_} {close}"
  | items => s!"{open_} {", ".intercalate items} {close}"

mutual

def Expr.source : Expr → String
  | .ident _ name => name
  | .number _ text | .bigint _ text => text
  | .string _ value => quote value
  | .bool _ b => if b then "true" else "false"
  | .null _ => "null"
  | .array _ elems => enclose "[" "]" (Expr.sources elems)
  | .object _ props => enclose "{" "}" (Property.sources props)
  | .paren _ inner => s!"( {inner.source} )"
  | .member _ obj name => s!"{obj.source} . {name}"
  | .index _ obj idx => s!"{obj.source} [ {idx.source} ]"
  | .call _ callee args => s!"{callee.source} {enclose "(" ")" (Expr.sources args)}"
  | .unary _ op arg => s!"{op.symbol} {arg.source}"
  | .prefix _ op arg => s!"{op.symbol} {arg.source}"
  | .postfix _ op arg => s!"{arg.source} {op.symbol}"
  | .binary _ op lhs rhs => s!"{lhs.source} {op.symbol} {rhs.source}"
  | .cond _ test a b => s!"{test.source} ? {a.source} : {b.source}"
  | .assign _ op target value => s!"{target.source} {op.symbol} {value.source}"

def Expr.sources : List Expr → List String
  | [] => []
  | e :: es => e.source :: Expr.sources es

def Property.source : Property → String
  | .shorthand _ name => name
  | .keyValue _ key value => s!"{key.source} : {value.source}"

def Property.sources : List Property → List String
  | [] => []
  | p :: ps => p.source :: Property.sources ps

end

def VarDecl.source (d : VarDecl) : String :=
  let type := match d.type with
    | some t => s!" : {t.source}"
    | none => ""
  let init := match d.init with
    | some e => s!" = {e.source}"
    | none => ""
  s!"{d.kind.keyword} {d.name}{type}{init} ;"

/-- `lines`, each two spaces further in. -/
def indent (lines : List String) : List String := lines.map ("  " ++ ·)

mutual

/-- The lines of a statement. -/
def Stmt.lines : Stmt → List String
  | .varDecl _ d => [d.source]
  | .exprStmt _ e => [s!"{e.source} ;"]
  | .returnStmt _ none => ["return ;"]
  | .returnStmt _ (some e) => [s!"return {e.source} ;"]
  | .ifStmt _ test t none => s!"if ( {test.source} )" :: indent t.lines
  | .ifStmt _ test t (some e) =>
    s!"if ( {test.source} )" :: indent t.lines ++ "else" :: indent e.lines
  | .forOfStmt _ kind name iterable body =>
    s!"for ( {kind.keyword} {name} of {iterable.source} )" :: indent body.lines
  | .whileStmt _ test body => s!"while ( {test.source} )" :: indent body.lines
  | .block _ body => "{" :: indent (Stmt.linesOf body) ++ ["}"]
  | .breakStmt _ => ["break ;"]
  | .continueStmt _ => ["continue ;"]
  | .empty _ => [";"]

def Stmt.linesOf : List Stmt → List String
  | [] => []
  | s :: ss => s.lines ++ Stmt.linesOf ss

end

def Param.source (p : Param) : String :=
  match p.type with
  | some t => s!"{p.name} : {t.source}"
  | none => p.name

def Field.source (f : Field) : String :=
  let readonly := if f.readonly then "readonly " else ""
  let optional := if f.optional then " ?" else ""
  s!"{readonly}{f.name}{optional} : {f.type.source} ;"

def ImportName.source (n : ImportName) : String :=
  if n.typeOnly then s!"type {n.name}" else n.name

def exportWord (exported : Bool) : String := if exported then "export " else ""

def Decl.lines : Decl → List String
  | .import _ names source =>
    [s!"import {enclose "{" "}" (names.map ImportName.source)} from {quote source} ;"]
  | .function _ exported name params returnType body =>
    let ret := match returnType with
      | some t => s!" : {t.source}"
      | none => ""
    s!"{exportWord exported}function {name} {enclose "(" ")" (params.map Param.source)}{ret}" ::
      body.lines
  | .interface _ exported name fields =>
    s!"{exportWord exported}interface {name} \{" :: indent (fields.map Field.source) ++ ["}"]
  | .typeAlias _ exported name type => [s!"{exportWord exported}type {name} = {type.source} ;"]
  | .exportedVar _ d => [s!"export {d.source}"]
  | .stmt s => s.lines

/-- The module as source, one line for each statement, ending in a line
break. -/
def Module.source (m : Module) : String :=
  String.join ((m.decls.flatMap Decl.lines).map (· ++ "\n"))

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
