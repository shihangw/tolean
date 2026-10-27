import tolean.Sexp
import tolean.TypeScript.Syntax.Ast

/-!
The S-expression form of a TypeScript syntax tree (see `tolean.Sexp`).
`tests/typescript/tscAst.ts` prints `tsc`'s tree in the same form; the two must
agree on every file that both accept.

Names come first among the atoms, then flags such as `export`, `readonly` and
`optional`, so that a name such as `readonly` cannot pass for a flag.
-/
namespace tolean.TypeScript.Syntax

open tolean

private def node (head : String) (span : Span) (atoms : List String) (children : List Sexp) :
    Sexp :=
  .node head (some span) atoms children

private def flag (on : Bool) (name : String) : List String := if on then [name] else []

def LitType.atom : LitType → String
  | .string value => Sexp.quote value
  | .number text | .bigint text => text
  | .bool value => if value then "true" else "false"

def PropKey.atom : PropKey → String
  | .ident name => name
  | .string value => Sexp.quote value
  | .number text => text

partial def TypeExpr.toSexp : TypeExpr → Sexp
  | .keyword s name => node "type-keyword" s [name] []
  | .null s => node "type-null" s [] []
  | .literal s lit => node "type-literal" s [lit.atom] []
  | .ref s name args => node "type-ref" s [name] (args.map toSexp)
  | .array s elem => node "type-array" s [] [elem.toSexp]
  | .union s members => node "type-union" s [] (members.map toSexp)
  | .paren s inner => node "type-paren" s [] [inner.toSexp]

mutual

partial def Expr.toSexp : Expr → Sexp
  | .ident s name => node "ident" s [name] []
  | .number s text => node "number" s [text] []
  | .bigint s text => node "bigint" s [text] []
  | .string s value => node "string" s [Sexp.quote value] []
  | .bool s value => node (if value then "true" else "false") s [] []
  | .null s => node "null" s [] []
  | .array s elems => node "array" s [] (elems.map Expr.toSexp)
  | .object s props => node "object" s [] (props.map Property.toSexp)
  | .paren s inner => node "paren" s [] [inner.toSexp]
  | .member s obj name => node "member" s [name] [obj.toSexp]
  | .index s obj idx => node "index" s [] [obj.toSexp, idx.toSexp]
  | .call s callee args => node "call" s [] (callee.toSexp :: args.map Expr.toSexp)
  | .unary s op arg => node "unary" s [op.symbol] [arg.toSexp]
  | .prefix s op arg => node "prefix" s [op.symbol] [arg.toSexp]
  | .postfix s op arg => node "postfix" s [op.symbol] [arg.toSexp]
  | .binary s op lhs rhs => node "binary" s [op.symbol] [lhs.toSexp, rhs.toSexp]
  | .cond s test ifTrue ifFalse => node "cond" s [] [test.toSexp, ifTrue.toSexp, ifFalse.toSexp]
  | .assign s op target value => node "assign" s [op.symbol] [target.toSexp, value.toSexp]

partial def Property.toSexp : Property → Sexp
  | .shorthand s name => node "shorthand" s [name] []
  | .keyValue s key value => node "property" s [key.atom] [value.toSexp]

end

def VarDecl.toSexp (span : Span) (exported : Bool) (d : VarDecl) : Sexp :=
  node d.kind.keyword span ([d.name] ++ flag exported "export")
    ((d.type.map TypeExpr.toSexp).toList ++ (d.init.map Expr.toSexp).toList)

partial def Stmt.toSexp : Stmt → Sexp
  | .varDecl s d => d.toSexp s false
  | .exprStmt s e => node "expr" s [] [e.toSexp]
  | .returnStmt s value => node "return" s [] (value.map Expr.toSexp).toList
  | .ifStmt s test thenBranch elseBranch =>
    node "if" s [] ([test.toSexp, thenBranch.toSexp] ++ (elseBranch.map toSexp).toList)
  | .forOfStmt s kind name iterable body =>
    node "for-of" s [kind.keyword, name] [iterable.toSexp, body.toSexp]
  | .whileStmt s test body => node "while" s [] [test.toSexp, body.toSexp]
  | .block s body => node "block" s [] (body.map toSexp)
  | .breakStmt s => node "break" s [] []
  | .continueStmt s => node "continue" s [] []
  | .empty s => node "empty" s [] []

def Param.toSexp (p : Param) : Sexp :=
  node "param" p.span [p.name] (p.type.map TypeExpr.toSexp).toList

def Field.toSexp (f : Field) : Sexp :=
  node "field" f.span ([f.name] ++ flag f.readonly "readonly" ++ flag f.optional "optional")
    [f.type.toSexp]

def Decl.toSexp : Decl → Sexp
  | .import s names source =>
    node "import" s [Sexp.quote source]
      (names.map fun n => node "name" n.span ([n.name] ++ flag n.typeOnly "type") [])
  | .function s exported name params returnType body =>
    node "function" s ([name] ++ flag exported "export")
      (params.map Param.toSexp ++ (returnType.map TypeExpr.toSexp).toList ++ [body.toSexp])
  | .interface s exported name fields =>
    node "interface" s ([name] ++ flag exported "export") (fields.map Field.toSexp)
  | .typeAlias s exported name type =>
    node "type" s ([name] ++ flag exported "export") [type.toSexp]
  | .exportedVar s d => d.toSexp s true
  | .stmt st => st.toSexp

def Module.toSexp (m : Module) : Sexp := .node "module" none [] (m.decls.map Decl.toSexp)

end tolean.TypeScript.Syntax
