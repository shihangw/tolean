import tolean.Sexp
import tolean.Go.Syntax.Ast

/-!
The S-expression form of a Go syntax tree (see `tolean.Sexp`).
`tests/go/goast` prints the tree from `go/parser` in the same form; the two
must agree on every file that both accept.
-/
namespace tolean.Go.Syntax

open tolean

private def node (head : String) (span : Span) (atoms : List String) (children : List Sexp) :
    Sexp :=
  .node head (some span) atoms children

/-- A part of its parent without a span, such as the init statement of `if`. -/
private def group (head : String) (children : List Sexp) : Sexp :=
  .node head none [] children

private def optGroup {A : Type} (head : String) (f : A → Sexp) : Option A → List Sexp
  | some x => [group head [f x]]
  | none => []

mutual

partial def Expr.toSexp : Expr → Sexp
  | .ident s name => node "ident" s [name] []
  | .lit s kind raw => node "lit" s [kind.name, Sexp.quote raw] []
  | .composite s type elts =>
    node "composite" s [] (optGroup "type" Expr.toSexp type ++ elts.map Expr.toSexp)
  | .keyValue s k v => node "key-value" s [] [k.toSexp, v.toSexp]
  | .paren s inner => node "paren" s [] [inner.toSexp]
  | .selector s obj name => node "selector" s [name] [obj.toSexp]
  | .index s obj idx => node "index" s [] [obj.toSexp, idx.toSexp]
  | .sliceExpr s obj low high =>
    node "slice-expr" s []
      ([obj.toSexp] ++ optGroup "low" Expr.toSexp low ++ optGroup "high" Expr.toSexp high)
  | .call s callee args ellipsis =>
    node "call" s (if ellipsis then ["..."] else []) (callee.toSexp :: args.map Expr.toSexp)
  | .star s inner => node "star" s [] [inner.toSexp]
  | .unary s op arg => node "unary" s [op] [arg.toSexp]
  | .binary s op lhs rhs => node "binary" s [op] [lhs.toSexp, rhs.toSexp]
  | .sliceType s elem => node "slice-type" s [] [elem.toSexp]
  | .arrayType s len elem => node "array-type" s [] [len.toSexp, elem.toSexp]
  | .mapType s k v => node "map-type" s [] [k.toSexp, v.toSexp]
  | .structType s fields => node "struct-type" s [] (fields.map Field.toSexp)
  | .interfaceType s methods => node "interface-type" s [] (methods.map Field.toSexp)
  | .funcType s params results => node "func-type" s [] (signatureSexp params results)
  | .ellipsis s elem => node "ellipsis" s [] [elem.toSexp]
  | .typeAssert s obj type => node "type-assert" s [] ([obj.toSexp] ++ (type.map Expr.toSexp).toList)
  | .funcLit s type body => node "func-lit" s [] [type.toSexp, body.toSexp]

partial def Field.toSexp : Field → Sexp
  | .mk s names type tag => node "field" s names ([type.toSexp] ++ (tag.map Expr.toSexp).toList)

partial def signatureSexp (params : List Field) (results : Option (List Field)) : List Sexp :=
  [group "params" (params.map Field.toSexp)] ++
    (results.map fun r => group "results" (r.map Field.toSexp)).toList

partial def Spec.toSexp : Spec → Sexp
  | .import s raw name => node "import-spec" s ([Sexp.quote raw] ++ name.toList) []
  | .type s name ty alias =>
    node (if alias then "alias-spec" else "type-spec") s [name] [ty.toSexp]
  | .value s names ty values =>
    node "value-spec" s names
      (optGroup "type" Expr.toSexp ty ++
        (if values.isEmpty then [] else [group "values" (values.map Expr.toSexp)]))

partial def GenDecl.toSexp : GenDecl → Sexp
  | .mk s keyword specs => node s!"decl-{keyword}" s [] (specs.map Spec.toSexp)

partial def Stmt.toSexp : Stmt → Sexp
  | .block s body => node "block" s [] (body.map Stmt.toSexp)
  | .expr s e => node "expr" s [] [e.toSexp]
  | .assign s op lhs rhs =>
    node "assign" s [op] [group "lhs" (lhs.map Expr.toSexp), group "rhs" (rhs.map Expr.toSexp)]
  | .incDec s op target => node "inc-dec" s [op] [target.toSexp]
  | .decl s d => node "decl-stmt" s [] [d.toSexp]
  | .ret s results => node "return" s [] (results.map Expr.toSexp)
  | .brk s => node "break" s [] []
  | .cont s => node "continue" s [] []
  | .ifStmt s init cond body els =>
    node "if" s []
      (optGroup "init" Stmt.toSexp init ++ [cond.toSexp, body.toSexp] ++
        optGroup "else" Stmt.toSexp els)
  | .forStmt s init cond post body =>
    node "for" s []
      (optGroup "init" Stmt.toSexp init ++ optGroup "cond" Expr.toSexp cond ++
        optGroup "post" Stmt.toSexp post ++ [body.toSexp])
  | .range s op key value iterable body =>
    node "range" s op.toList
      (optGroup "key" Expr.toSexp key ++ optGroup "value" Expr.toSexp value ++
        [iterable.toSexp, body.toSexp])
  | .switchStmt s init tag bodySpan clauses =>
    node "switch" s []
      (optGroup "init" Stmt.toSexp init ++ optGroup "tag" Expr.toSexp tag ++
        [node "block" bodySpan [] (clauses.map CaseClause.toSexp)])
  | .typeSwitch s init guard bodySpan clauses =>
    node "type-switch" s []
      (optGroup "init" Stmt.toSexp init ++ [group "assign" [guard.toSexp]] ++
        [node "block" bodySpan [] (clauses.map CaseClause.toSexp)])
  | .deferStmt s call => node "defer" s [] [call.toSexp]

partial def CaseClause.toSexp : CaseClause → Sexp
  | .mk s exprs body =>
    node "case" s (if exprs.isNone then ["default"] else [])
      ([group "exprs" ((exprs.getD []).map Expr.toSexp)] ++ body.map Stmt.toSexp)

end

def Decl.toSexp : Decl → Sexp
  | .func s recv name params results body =>
    node "func" s [name]
      ((recv.map fun r => group "recv" (r.map Field.toSexp)).toList ++
        signatureSexp params results ++ [body.toSexp])
  | .gen d => d.toSexp

def File.toSexp (f : File) : Sexp := .node "file" none [f.package] (f.decls.map Decl.toSexp)

end tolean.Go.Syntax
