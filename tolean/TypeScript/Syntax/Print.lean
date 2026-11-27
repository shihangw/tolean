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
  | .indexed s receiver key => node "type-indexed" s [Sexp.quote key] [receiver.toSexp]
  | .union s members => node "type-union" s [] (members.map toSexp)
  | .paren s inner => node "type-paren" s [] [inner.toSexp]
  | .tuple s readonly elems => node "type-tuple" s (flag readonly "readonly") (elems.map toSexp)
  | .object s fields => node "type-object" s [] (fields.map fun
      | .field sp readonly name optional type =>
        node "type-field" sp ([name] ++ flag readonly "readonly" ++ flag optional "optional")
          [type.toSexp])
  | .predicate s parameter target => node "type-predicate" s [parameter] [target.toSexp]

def Param.toSexp (p : Param) : Sexp :=
  node "param" p.span ([p.name] ++ flag p.optional "optional") (p.type.map TypeExpr.toSexp).toList

def CtorParam.toSexp (p : CtorParam) : Sexp :=
  node "param" p.param.span ([p.param.name] ++ flag p.param.optional "optional" ++ flag p.readonly "readonly")
    (p.param.type.map TypeExpr.toSexp).toList

mutual

partial def Expr.toSexp : Expr → Sexp
  | .ident s name => node "ident" s [name] []
  | .number s text => node "number" s [text] []
  | .bigint s text => node "bigint" s [text] []
  | .string s value => node "string" s [Sexp.quote value] []
  | .regexp s source _ => node "regexp" s [Sexp.quote source] []
  | .bool s value => node (if value then "true" else "false") s [] []
  | .null s => node "null" s [] []
  | .this s => node "this" s [] []
  | .array s elems => node "array" s [] (elems.map Expr.toSexp)
  | .object s props => node "object" s [] (props.map Property.toSexp)
  | .paren s inner => node "paren" s [] [inner.toSexp]
  | .member s obj name => node "member" s [name] [obj.toSexp]
  | .optMember s obj name => node "optMember" s [name] [obj.toSexp]
  | .index s obj idx => node "index" s [] [obj.toSexp, idx.toSexp]
  | .optIndex s obj idx => node "optIndex" s [] [obj.toSexp, idx.toSexp]
  | .call s callee args => node "call" s [] (callee.toSexp :: args.map Expr.toSexp)
  | .unary s op arg => node "unary" s [op.symbol] [arg.toSexp]
  | .prefix s op arg => node "prefix" s [op.symbol] [arg.toSexp]
  | .postfix s op arg => node "postfix" s [op.symbol] [arg.toSexp]
  | .binary s op lhs rhs => node "binary" s [op.symbol] [lhs.toSexp, rhs.toSexp]
  | .cond s test ifTrue ifFalse => node "cond" s [] [test.toSexp, ifTrue.toSexp, ifFalse.toSexp]
  | .assign s op target value => node "assign" s [op.symbol] [target.toSexp, value.toSexp]
  | .arrow s _ params body => node "arrow" s [] (params.map Param.toSexp ++ [body.toSexp])
  | .asConst s e => node "asConst" s [] [e.toSexp]
  | .satisfies s e type => node "satisfies" s [] [e.toSexp, type.toSexp]
  | .new s callee typeArgs args =>
    node "new" s [callee] (typeArgs.map TypeExpr.toSexp ++ args.map Expr.toSexp)
  | .spread s e => node "spread" s [] [e.toSexp]

partial def Property.toSexp : Property → Sexp
  | .shorthand s name => node "shorthand" s [name] []
  | .keyValue s key value => node "property" s [key.atom] [value.toSexp]
  | .spread s value => node "spread" s [] [value.toSexp]

end

def VarDecl.children (d : VarDecl) : List Sexp :=
  (d.type.map TypeExpr.toSexp).toList ++ (d.init.map Expr.toSexp).toList

def VarDecl.toSexp (span : Span) (exported : Bool) (d : VarDecl) : Sexp :=
  node d.kind.keyword span ([d.name] ++ flag exported "export") d.children

/-- `[a, , ...r]` as `(array-pattern (name a) (hole) (rest r))`. -/
def ArrayPattern.toSexp (p : ArrayPattern) : Sexp :=
  .node "array-pattern" none [] (p.elems.map (fun
    | some n => .node "name" none [n] []
    | none => .node "hole" none [] []) ++ p.rest.toList.map fun n => .node "rest" none [n] [])

partial def Stmt.toSexp : Stmt → Sexp
  | .varDecl s d => d.toSexp s false
  | .destructure s kind p type init =>
    node kind.keyword s [] ([p.toSexp] ++ (type.map TypeExpr.toSexp).toList ++ [init.toSexp])
  | .objectDestructure s kind p type init =>
    node kind.keyword s [] ([node "object-pattern" p.span [] [p.toSexp]] ++
      (type.map TypeExpr.toSexp).toList ++ [init.toSexp])
  | .exprStmt s e => node "expr" s [] [e.toSexp]
  | .returnStmt s value => node "return" s [] (value.map Expr.toSexp).toList
  | .throwStmt s value => node "throw" s [] [value.toSexp]
  | .tryCatch s body name handler => node "try" s [name] [body.toSexp, handler.toSexp]
  | .ifStmt s test thenBranch elseBranch =>
    node "if" s [] ([test.toSexp, thenBranch.toSexp] ++ (elseBranch.map toSexp).toList)
  | .forOfStmt s kind name iterable body =>
    node "for-of" s [kind.keyword, name] [iterable.toSexp, body.toSexp]
  | .forOfPattern s kind p iterable body =>
    node "for-of" s [kind.keyword] [p.toSexp, iterable.toSexp, body.toSexp]
  -- The three parts keep no span, so their nodes have none. Each holds its
  -- part, or nothing when the part is absent.
  | .forStmt s init test update body =>
    node "for" s [] [
      .node "init" none [] (init.map fun d => Sexp.node d.kind.keyword none [d.name] d.children).toList,
      .node "test" none [] (test.map Expr.toSexp).toList,
      .node "update" none [] (update.map Expr.toSexp).toList,
      body.toSexp]
  | .whileStmt s test body => node "while" s [] [test.toSexp, body.toSexp]
  | .block s body => node "block" s [] (body.map toSexp)
  | .breakStmt s => node "break" s [] []
  | .continueStmt s => node "continue" s [] []
  | .empty s => node "empty" s [] []
  -- A clause keeps no span, so its node has none.
  | .switchStmt s disc clauses =>
    node "switch" s [] (disc.toSexp :: clauses.map fun (test, body) =>
      .node (if test.isSome then "case" else "default") none []
        ((test.map Expr.toSexp).toList ++ body.map toSexp))
  -- As a function at the top level prints, without `export`.
  | .funDecl s name typeParams params returnType body =>
    node "function" s [name]
      (typeParams.map (fun t => .node "type-param" none [t] []) ++ params.map Param.toSexp ++
        (returnType.map TypeExpr.toSexp).toList ++ [body.toSexp])

def Field.toSexp (f : Field) : Sexp :=
  node "field" f.span ([f.name] ++ flag f.readonly "readonly" ++ flag f.optional "optional")
    [f.type.toSexp]

def ClassMethod.toSexp (m : ClassMethod) : Sexp :=
  node "method" m.span [m.name]
    (m.params.map Param.toSexp ++ (m.returnType.map TypeExpr.toSexp).toList ++ [m.body.toSexp])

def ClassMember.toSexp : ClassMember → Sexp
  | .field f => f.toSexp
  | .ctor params body => .node "constructor" none [] (params.map CtorParam.toSexp ++ [body.toSexp])
  | .method m => m.toSexp

/-- A name of an import or an export list: the name, `type` if it is a type,
and `as` with the other name if it is renamed. -/
def ImportName.toSexp (n : ImportName) : Sexp :=
  node "name" n.span ([n.name] ++ flag n.typeOnly "type" ++ (n.alias.map fun a => ["as", a]).getD []) []

def Decl.toSexp : Decl → Sexp
  | .import s names source =>
    node "import" s [Sexp.quote source]
      (names.map ImportName.toSexp)
  | .function s exported name typeParams params returnType body =>
    -- A type parameter keeps no span, so its node has none.
    node "function" s ([name] ++ flag exported "export")
      (typeParams.map (fun t => .node "type-param" none [t] []) ++ params.map Param.toSexp ++
        (returnType.map TypeExpr.toSexp).toList ++ [body.toSexp])
  | .interface s exported name typeParams fields =>
    node "interface" s ([name] ++ flag exported "export")
      (typeParams.map (fun t => .node "type-param" none [t] []) ++ fields.map Field.toSexp)
  | .typeAlias s exported name typeParams type =>
    node "type" s ([name] ++ flag exported "export")
      (typeParams.map (fun t => .node "type-param" none [t] []) ++ [type.toSexp])
  | .enum s exported name members =>
    node "enum" s ([name] ++ flag exported "export")
      (members.map fun m => node "member" m.span [m.name, Sexp.quote m.value] [])
  | .classDecl d =>
    node "class" d.span ([d.name] ++ flag d.exported "export")
      (d.members.map ClassMember.toSexp)
  -- The constructor's parameters, then the message. A class without a
  -- constructor has no children.
  | .errorClass s exported name ctor =>
    node "class" s ([name] ++ flag exported "export")
      ((ctor.map fun (ps, m, n) => ps.map CtorParam.toSexp ++ [m.toSexp] ++
        n.toList.map (fun name => .node "error-name" none [Sexp.quote name] [])).getD [])
  | .exports s names source =>
    node "export" s (source.map Sexp.quote).toList
      (names.map ImportName.toSexp)
  | .exportedVar s d => d.toSexp s true
  | .stmt st => st.toSexp

def Module.toSexp (m : Module) : Sexp := .node "module" none [] (m.decls.map Decl.toSexp)

end tolean.TypeScript.Syntax
