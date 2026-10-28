import tolean.TypeScript.Syntax.Ast
import tolean.TypeScript.Syntax.Print

/-!
The syntax tree as a Lean term. `tolean certify` writes the parsed program
with these functions, so that a certificate can state facts about the exact
tree the parser returned.

Each constructor prints as itself, with its full name, and each span prints
as `sp startLine startCol stopLine stopCol`. The functions are total, so the
printer covers every tree.
-/
namespace tolean.TypeScript.Certify

open tolean tolean.TypeScript.Syntax

def str (s : String) : String := Sexp.quote s

def span (s : Span) : String := s!"(sp {s.start.line} {s.start.col} {s.stop.line} {s.stop.col})"

def list (items : List String) : String := "[" ++ ", ".intercalate items ++ "]"

def option (o : Option String) : String :=
  match o with
  | some x => s!"(some {x})"
  | none => "none"

def ns : String := "tolean.TypeScript.Syntax."

def binOp (op : BinOp) : String :=
  ns ++ "BinOp." ++ match op with
  | .coalesce => "coalesce" | .or => "or" | .and => "and" | .bitOr => "bitOr"
  | .bitXor => "bitXor" | .bitAnd => "bitAnd" | .looseEq => "looseEq" | .looseNe => "looseNe"
  | .strictEq => "strictEq" | .strictNe => "strictNe" | .lt => "lt" | .gt => "gt" | .le => "le"
  | .ge => "ge" | .instanceof => "instanceof" | .«in» => "«in»" | .shl => "shl" | .shr => "shr"
  | .ushr => "ushr" | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div"
  | .mod => "mod" | .exp => "exp"

def unaryOp (op : UnaryOp) : String :=
  ns ++ "UnaryOp." ++ match op with
  | .not => "not" | .neg => "neg" | .plus => "plus" | .bitNot => "bitNot"
  | .typeof => "typeof" | .void => "void"

def updateOp (op : UpdateOp) : String :=
  ns ++ "UpdateOp." ++ match op with
  | .increment => "increment" | .decrement => "decrement"

def assignOp (op : AssignOp) : String :=
  ns ++ "AssignOp." ++ match op with
  | .assign => "assign" | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div"
  | .mod => "mod" | .exp => "exp" | .shl => "shl" | .shr => "shr" | .ushr => "ushr"
  | .bitAnd => "bitAnd" | .bitOr => "bitOr" | .bitXor => "bitXor" | .and => "and"
  | .or => "or" | .coalesce => "coalesce"

def litType (l : LitType) : String :=
  match l with
  | .string v => s!"({ns}LitType.string {str v})"
  | .number t => s!"({ns}LitType.number {str t})"
  | .bigint t => s!"({ns}LitType.bigint {str t})"
  | .bool b => s!"({ns}LitType.bool {b})"

def typeExpr : TypeExpr → String
  | .keyword s n => s!"({ns}TypeExpr.keyword {span s} {str n})"
  | .null s => s!"({ns}TypeExpr.null {span s})"
  | .literal s l => s!"({ns}TypeExpr.literal {span s} {litType l})"
  | .ref s n args => s!"({ns}TypeExpr.ref {span s} {str n} {list (args.map typeExpr)})"
  | .array s e => s!"({ns}TypeExpr.array {span s} {typeExpr e})"
  | .union s ms => s!"({ns}TypeExpr.union {span s} {list (ms.map typeExpr)})"
  | .paren s e => s!"({ns}TypeExpr.paren {span s} {typeExpr e})"

def propKey (k : PropKey) : String :=
  match k with
  | .ident n => s!"({ns}PropKey.ident {str n})"
  | .string v => s!"({ns}PropKey.string {str v})"
  | .number t => s!"({ns}PropKey.number {str t})"

mutual

def expr : Expr → String
  | .ident s n => s!"({ns}Expr.ident {span s} {str n})"
  | .number s t => s!"({ns}Expr.number {span s} {str t})"
  | .bigint s t => s!"({ns}Expr.bigint {span s} {str t})"
  | .string s v => s!"({ns}Expr.string {span s} {str v})"
  | .bool s b => s!"({ns}Expr.bool {span s} {b})"
  | .null s => s!"({ns}Expr.null {span s})"
  | .array s es => s!"({ns}Expr.array {span s} {list (exprs es)})"
  | .object s ps => s!"({ns}Expr.object {span s} {list (props ps)})"
  | .paren s e => s!"({ns}Expr.paren {span s} {expr e})"
  | .member s o n => s!"({ns}Expr.member {span s} {expr o} {str n})"
  | .index s o i => s!"({ns}Expr.index {span s} {expr o} {expr i})"
  | .call s c as => s!"({ns}Expr.call {span s} {expr c} {list (exprs as)})"
  | .unary s op a => s!"({ns}Expr.unary {span s} {unaryOp op} {expr a})"
  | .prefix s op a => s!"({ns}Expr.prefix {span s} {updateOp op} {expr a})"
  | .postfix s op a => s!"({ns}Expr.postfix {span s} {updateOp op} {expr a})"
  | .binary s op l r => s!"({ns}Expr.binary {span s} {binOp op} {expr l} {expr r})"
  | .cond s t a b => s!"({ns}Expr.cond {span s} {expr t} {expr a} {expr b})"
  | .assign s op t v => s!"({ns}Expr.assign {span s} {assignOp op} {expr t} {expr v})"

def exprs : List Expr → List String
  | [] => []
  | e :: es => expr e :: exprs es

def props : List Property → List String
  | [] => []
  | .shorthand s n :: ps => s!"({ns}Property.shorthand {span s} {str n})" :: props ps
  | .keyValue s k v :: ps => s!"({ns}Property.keyValue {span s} {propKey k} {expr v})" :: props ps

end

def varKind : VarKind → String
  | .const => s!"{ns}VarKind.const"
  | .«let» => s!"{ns}VarKind.«let»"

def varDecl (d : VarDecl) : String :=
  s!"\{ kind := {varKind d.kind}, name := {str d.name}, type := {option (d.type.map typeExpr)}, " ++
    s!"init := {option (d.init.map expr)} }"

mutual

def stmt : Stmt → String
  | .varDecl s d => s!"({ns}Stmt.varDecl {span s} {varDecl d})"
  | .exprStmt s e => s!"({ns}Stmt.exprStmt {span s} {expr e})"
  | .returnStmt s v => s!"({ns}Stmt.returnStmt {span s} {option (v.map expr)})"
  | .ifStmt s t a b =>
    s!"({ns}Stmt.ifStmt {span s} {expr t} {stmt a} {option (optStmt b)})"
  | .forOfStmt s k n i b =>
    s!"({ns}Stmt.forOfStmt {span s} {varKind k} {str n} {expr i} {stmt b})"
  | .whileStmt s t b => s!"({ns}Stmt.whileStmt {span s} {expr t} {stmt b})"
  | .block s body => s!"({ns}Stmt.block {span s} {list (stmts body)})"
  | .breakStmt s => s!"({ns}Stmt.breakStmt {span s})"
  | .continueStmt s => s!"({ns}Stmt.continueStmt {span s})"
  | .empty s => s!"({ns}Stmt.empty {span s})"

def optStmt : Option Stmt → Option String
  | some s => some (stmt s)
  | none => none

def stmts : List Stmt → List String
  | [] => []
  | s :: ss => stmt s :: stmts ss

end

def param (p : Param) : String :=
  s!"\{ span := {span p.span}, name := {str p.name}, type := {option (p.type.map typeExpr)} }"

def field (f : Field) : String :=
  s!"\{ span := {span f.span}, readonly := {f.readonly}, name := {str f.name}, " ++
    s!"optional := {f.optional}, type := {typeExpr f.type} }"

def importName (n : ImportName) : String :=
  s!"\{ span := {span n.span}, typeOnly := {n.typeOnly}, name := {str n.name} }"

def decl : Decl → String
  | .import s names source => s!"({ns}Decl.import {span s} {list (names.map importName)} {str source})"
  | .function s e n ps r b =>
    s!"({ns}Decl.function {span s} {e} {str n} {list (ps.map param)} " ++
      s!"{option (r.map typeExpr)}\n    {stmt b})"
  | .interface s e n fs => s!"({ns}Decl.interface {span s} {e} {str n} {list (fs.map field)})"
  | .typeAlias s e n t => s!"({ns}Decl.typeAlias {span s} {e} {str n} {typeExpr t})"
  | .exportedVar s d => s!"({ns}Decl.exportedVar {span s} {varDecl d})"
  | .stmt s => s!"({ns}Decl.stmt {stmt s})"

/-- The module as a Lean term. -/
def module (m : Module) : String :=
  "{ decls := [\n  " ++ ",\n  ".intercalate (m.decls.map decl) ++ "] }"

end tolean.TypeScript.Certify
