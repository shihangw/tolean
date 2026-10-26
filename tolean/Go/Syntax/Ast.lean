import tolean.Go.Syntax.Token

/-!
The Go syntax tree. It follows `go/ast` for the syntax that Tolean reads, and
every node's span is the one `go/ast` gives it, from `Pos()` to `End()`.

The parser reads more than the translator supports, such as type switches and
function literals, so that a file can be read when only some of its
declarations are translated.
-/
namespace tolean.Go.Syntax

open tolean

mutual

inductive Expr where
  | ident (span : Span) (name : String)
  | lit (span : Span) (kind : LitKind) (raw : String)
  | composite (span : Span) (type : Option Expr) (elts : List Expr)
  | keyValue (span : Span) (key value : Expr)
  | paren (span : Span) (inner : Expr)
  | selector (span : Span) (obj : Expr) (name : String)
  | index (span : Span) (obj idx : Expr)
  | sliceExpr (span : Span) (obj : Expr) (low high : Option Expr)
  | call (span : Span) (callee : Expr) (args : List Expr) (ellipsis : Bool)
  /-- `*x`: a pointer type, or a dereference. -/
  | star (span : Span) (inner : Expr)
  | unary (span : Span) (op : String) (arg : Expr)
  | binary (span : Span) (op : String) (lhs rhs : Expr)
  | sliceType (span : Span) (elem : Expr)
  | arrayType (span : Span) (len elem : Expr)
  | mapType (span : Span) (key value : Expr)
  | structType (span : Span) (fields : List Field)
  | interfaceType (span : Span) (methods : List Field)
  | funcType (span : Span) (params : List Field) (results : Option (List Field))
  /-- `...T` on the last parameter. -/
  | ellipsis (span : Span) (elem : Expr)
  /-- `x.(T)`, or `x.(type)` in a type switch when `type` is `none`. -/
  | typeAssert (span : Span) (obj : Expr) (type : Option Expr)
  | funcLit (span : Span) (type : Expr) (body : Stmt)

/-- A parameter, result, struct field or interface method. -/
inductive Field where
  | mk (span : Span) (names : List String) (type : Expr) (tag : Option Expr)

inductive Spec where
  | import (span : Span) (raw : String) (name : Option String)
  | type (span : Span) (name : String) (type : Expr) (alias : Bool)
  | value (span : Span) (names : List String) (type : Option Expr) (values : List Expr)

/-- `import`, `const`, `type` or `var`, with its specs. -/
inductive GenDecl where
  | mk (span : Span) (keyword : String) (specs : List Spec)

inductive Stmt where
  | block (span : Span) (body : List Stmt)
  | expr (span : Span) (e : Expr)
  /-- `=`, `:=`, `+=` and the other assignment operators. -/
  | assign (span : Span) (op : String) (lhs rhs : List Expr)
  | incDec (span : Span) (op : String) (target : Expr)
  | decl (span : Span) (d : GenDecl)
  | ret (span : Span) (results : List Expr)
  | brk (span : Span)
  | cont (span : Span)
  | ifStmt (span : Span) (init : Option Stmt) (cond : Expr) (body : Stmt) (els : Option Stmt)
  | forStmt (span : Span) (init : Option Stmt) (cond : Option Expr) (post : Option Stmt)
      (body : Stmt)
  /-- `for k, v := range x`. `op` is `:=`, `=`, or `none` for `for range x`. -/
  | range (span : Span) (op : Option String) (key value : Option Expr) (iterable : Expr)
      (body : Stmt)
  | switchStmt (span : Span) (init : Option Stmt) (tag : Option Expr) (bodySpan : Span)
      (clauses : List CaseClause)
  /-- `switch v := x.(type) {…}`. `guard` is the `v := x.(type)` or `x.(type)`
  statement, and the case expressions are types. -/
  | typeSwitch (span : Span) (init : Option Stmt) (guard : Stmt) (bodySpan : Span)
      (clauses : List CaseClause)
  | deferStmt (span : Span) (call : Expr)

inductive CaseClause where
  /-- `exprs` is `none` for `default`. -/
  | mk (span : Span) (exprs : Option (List Expr)) (body : List Stmt)

end

instance : Inhabited Expr := ⟨.ident default ""⟩
instance : Inhabited Stmt := ⟨.block default []⟩

def Expr.span : Expr → Span
  | .ident s .. | .lit s .. | .composite s .. | .keyValue s .. | .paren s ..
  | .selector s .. | .index s .. | .sliceExpr s .. | .call s .. | .star s ..
  | .unary s .. | .binary s .. | .sliceType s .. | .arrayType s .. | .mapType s ..
  | .structType s .. | .interfaceType s .. | .funcType s .. | .ellipsis s ..
  | .typeAssert s .. | .funcLit s .. => s

def GenDecl.span : GenDecl → Span | .mk s .. => s
def GenDecl.keyword : GenDecl → String | .mk _ k _ => k
def GenDecl.specs : GenDecl → List Spec | .mk _ _ ss => ss

def Stmt.span : Stmt → Span
  | .block s .. | .expr s .. | .assign s .. | .incDec s .. | .decl s .. | .ret s ..
  | .brk s | .cont s | .ifStmt s .. | .forStmt s .. | .range s .. | .switchStmt s ..
  | .typeSwitch s .. | .deferStmt s .. => s

inductive Decl where
  | func (span : Span) (recv : Option (List Field)) (name : String) (params : List Field)
      (results : Option (List Field)) (body : Stmt)
  | gen (d : GenDecl)

structure File where
  package : String
  decls : List Decl

end tolean.Go.Syntax
