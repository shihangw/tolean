import tolean.Source

/-!
The TypeScript syntax tree: the part of TypeScript that the parser reads.
Every node has its span. Parentheses stay in the tree as `paren` nodes, as in
`tsc`, so a printed tree shows how the source grouped each expression.
-/
namespace tolean.TypeScript.Syntax

open tolean

inductive BinOp where
  | coalesce | or | and | bitOr | bitXor | bitAnd
  | looseEq | looseNe | strictEq | strictNe
  | lt | gt | le | ge | instanceof | «in»
  | shl | shr | ushr
  | add | sub | mul | div | mod | exp
deriving BEq, Repr, Inhabited

def BinOp.symbol : BinOp → String
  | .coalesce => "??" | .or => "||" | .and => "&&"
  | .bitOr => "|" | .bitXor => "^" | .bitAnd => "&"
  | .looseEq => "==" | .looseNe => "!=" | .strictEq => "===" | .strictNe => "!=="
  | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">="
  | .instanceof => "instanceof" | .«in» => "in"
  | .shl => "<<" | .shr => ">>" | .ushr => ">>>"
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%" | .exp => "**"

/-- Higher binds tighter. `**` is right-associative; the others are
left-associative. -/
def BinOp.precedence : BinOp → Nat
  | .coalesce => 1
  | .or => 2
  | .and => 3
  | .bitOr => 4
  | .bitXor => 5
  | .bitAnd => 6
  | .looseEq | .looseNe | .strictEq | .strictNe => 7
  | .lt | .gt | .le | .ge | .instanceof | .«in» => 8
  | .shl | .shr | .ushr => 9
  | .add | .sub => 10
  | .mul | .div | .mod => 11
  | .exp => 12

def BinOp.all : List BinOp :=
  [.coalesce, .or, .and, .bitOr, .bitXor, .bitAnd, .looseEq, .looseNe, .strictEq,
   .strictNe, .lt, .gt, .le, .ge, .instanceof, .«in», .shl, .shr, .ushr, .add, .sub,
   .mul, .div, .mod, .exp]

def BinOp.ofSymbol? (s : String) : Option BinOp := BinOp.all.find? (·.symbol == s)

inductive UnaryOp where
  | not | neg | plus | bitNot | typeof | void
deriving BEq, Repr, Inhabited

def UnaryOp.symbol : UnaryOp → String
  | .not => "!" | .neg => "-" | .plus => "+" | .bitNot => "~"
  | .typeof => "typeof" | .void => "void"

inductive UpdateOp where
  | increment | decrement
deriving BEq, Repr, Inhabited

def UpdateOp.symbol : UpdateOp → String
  | .increment => "++" | .decrement => "--"

inductive AssignOp where
  | assign | add | sub | mul | div | mod | exp | shl | shr | ushr
  | bitAnd | bitOr | bitXor | and | or | coalesce
deriving BEq, Repr, Inhabited

def AssignOp.symbol : AssignOp → String
  | .assign => "=" | .add => "+=" | .sub => "-=" | .mul => "*=" | .div => "/="
  | .mod => "%=" | .exp => "**=" | .shl => "<<=" | .shr => ">>=" | .ushr => ">>>="
  | .bitAnd => "&=" | .bitOr => "|=" | .bitXor => "^=" | .and => "&&=" | .or => "||="
  | .coalesce => "??="

def AssignOp.all : List AssignOp :=
  [.assign, .add, .sub, .mul, .div, .mod, .exp, .shl, .shr, .ushr, .bitAnd, .bitOr,
   .bitXor, .and, .or, .coalesce]

def AssignOp.ofSymbol? (s : String) : Option AssignOp := AssignOp.all.find? (·.symbol == s)

/-- A literal type, such as `'a'`, `1` or `true`. -/
inductive LitType where
  | string (value : String)
  | number (text : String)
  | bigint (text : String)
  | bool (value : Bool)

inductive TypeExpr where
  /-- `number`, `bigint`, `boolean`, `string`, `void`, `undefined`, `any`,
  `unknown`, `never`, `object` or `symbol`. -/
  | keyword (span : Span) (name : String)
  | null (span : Span)
  | literal (span : Span) (lit : LitType)
  /-- A named type, with its type arguments: `Item`, `ReadonlyArray<Item>`. -/
  | ref (span : Span) (name : String) (args : List TypeExpr)
  /-- `T[]`. -/
  | array (span : Span) (elem : TypeExpr)
  | union (span : Span) (members : List TypeExpr)
  | paren (span : Span) (inner : TypeExpr)

/-- The key of an object literal property. -/
inductive PropKey where
  | ident (name : String)
  | string (value : String)
  | number (text : String)

mutual

inductive Expr where
  | ident (span : Span) (name : String)
  /-- As written in the source. -/
  | number (span : Span) (text : String)
  /-- As written in the source, with its `n`. -/
  | bigint (span : Span) (text : String)
  | string (span : Span) (value : String)
  | bool (span : Span) (value : Bool)
  | null (span : Span)
  | array (span : Span) (elems : List Expr)
  | object (span : Span) (props : List Property)
  | paren (span : Span) (inner : Expr)
  | member (span : Span) (obj : Expr) (name : String)
  | index (span : Span) (obj : Expr) (idx : Expr)
  | call (span : Span) (callee : Expr) (args : List Expr)
  | unary (span : Span) (op : UnaryOp) (arg : Expr)
  | prefix (span : Span) (op : UpdateOp) (arg : Expr)
  | postfix (span : Span) (op : UpdateOp) (arg : Expr)
  | binary (span : Span) (op : BinOp) (lhs rhs : Expr)
  | cond (span : Span) (test ifTrue ifFalse : Expr)
  | assign (span : Span) (op : AssignOp) (target value : Expr)

inductive Property where
  /-- `{ a }`. -/
  | shorthand (span : Span) (name : String)
  /-- `{ a: e }`. -/
  | keyValue (span : Span) (key : PropKey) (value : Expr)

end

instance : Inhabited Expr := ⟨.null default⟩

/-- `&&` or `||`, not in parentheses. -/
def Expr.isLogical : Expr → Bool
  | .binary _ .and _ _ | .binary _ .or _ _ => true
  | _ => false

/-- `??`, not in parentheses. -/
def Expr.isCoalesce : Expr → Bool
  | .binary _ .coalesce _ _ => true
  | _ => false

/-- A target that `=`, `++` and `--` can change. -/
def Expr.isSimpleTarget : Expr → Bool
  | .ident .. | .member .. | .index .. => true
  | .paren _ inner => inner.isSimpleTarget
  | _ => false

inductive VarKind where
  | const | «let»
deriving BEq, Repr, Inhabited

def VarKind.keyword : VarKind → String
  | .const => "const" | .«let» => "let"

/-- One `const` or `let` declaration. -/
structure VarDecl where
  kind : VarKind
  name : String
  type : Option TypeExpr
  init : Option Expr

inductive Stmt where
  | varDecl (span : Span) (decl : VarDecl)
  | exprStmt (span : Span) (expr : Expr)
  | returnStmt (span : Span) (value : Option Expr)
  | ifStmt (span : Span) (test : Expr) (thenBranch : Stmt) (elseBranch : Option Stmt)
  | forOfStmt (span : Span) (kind : VarKind) (name : String) (iterable : Expr) (body : Stmt)
  | whileStmt (span : Span) (test : Expr) (body : Stmt)
  | block (span : Span) (body : List Stmt)
  | breakStmt (span : Span)
  | continueStmt (span : Span)
  | empty (span : Span)

instance : Inhabited Stmt := ⟨.empty default⟩

structure Param where
  span : Span
  name : String
  type : Option TypeExpr

/-- A property of an interface. -/
structure Field where
  span : Span
  readonly : Bool
  name : String
  optional : Bool
  type : TypeExpr

inductive Decl where
  /-- `body` is a `block`. -/
  | function (span : Span) (exported : Bool) (name : String) (params : List Param)
      (returnType : Option TypeExpr) (body : Stmt)
  | interface (span : Span) (exported : Bool) (name : String) (fields : List Field)
  | typeAlias (span : Span) (exported : Bool) (name : String) (type : TypeExpr)
  | exportedVar (span : Span) (decl : VarDecl)
  | stmt (stmt : Stmt)

structure Module where
  decls : List Decl

-- These types have decidable equality. The ones that hold lists of
-- themselves get theirs in `Equality.lean`, because Lean cannot derive it.
deriving instance DecidableEq for BinOp
deriving instance DecidableEq for UnaryOp
deriving instance DecidableEq for UpdateOp
deriving instance DecidableEq for AssignOp
deriving instance DecidableEq for LitType
deriving instance DecidableEq for PropKey
deriving instance DecidableEq for VarKind

end tolean.TypeScript.Syntax

namespace tolean.TypeScript.Syntax

open tolean

def TypeExpr.span : TypeExpr → Span
  | .keyword s _ | .null s | .literal s _ | .ref s _ _ | .array s _ | .union s _ | .paren s _ => s

def Expr.span : Expr → Span
  | .ident s _ | .number s _ | .bigint s _ | .string s _ | .bool s _ | .null s | .array s _
  | .object s _ | .paren s _ | .member s _ _ | .index s _ _ | .call s _ _ | .unary s _ _
  | .prefix s _ _ | .postfix s _ _ | .binary s _ _ _ | .cond s _ _ _ | .assign s _ _ _ => s

def Stmt.span : Stmt → Span
  | .varDecl s _ | .exprStmt s _ | .returnStmt s _ | .ifStmt s _ _ _ | .forOfStmt s _ _ _ _
  | .whileStmt s _ _ | .block s _ | .breakStmt s | .continueStmt s | .empty s => s

def Decl.span : Decl → Span
  | .function s .. | .interface s .. | .typeAlias s .. | .exportedVar s _ => s
  | .stmt st => st.span

/-- `e` without the parentheses around it. -/
def Expr.stripParens : Expr → Expr
  | .paren _ inner => inner.stripParens
  | e => e

end tolean.TypeScript.Syntax
