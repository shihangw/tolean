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

/-- A parameter of a function or an arrow function. -/
structure Param where
  span : Span
  name : String
  type : Option TypeExpr

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
  /-- `obj?.name`: `undefined` when `obj` is `null` or `undefined`. -/
  | optMember (span : Span) (obj : Expr) (name : String)
  | index (span : Span) (obj : Expr) (idx : Expr)
  | call (span : Span) (callee : Expr) (args : List Expr)
  | unary (span : Span) (op : UnaryOp) (arg : Expr)
  | prefix (span : Span) (op : UpdateOp) (arg : Expr)
  | postfix (span : Span) (op : UpdateOp) (arg : Expr)
  | binary (span : Span) (op : BinOp) (lhs rhs : Expr)
  | cond (span : Span) (test ifTrue ifFalse : Expr)
  | assign (span : Span) (op : AssignOp) (target value : Expr)
  /-- `(a: T, b) => body`, or `a => body` when `parens` is false. The body is
  an expression. -/
  | arrow (span : Span) (parens : Bool) (params : List Param) (body : Expr)

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

/-- `=`, `+=`, `-=` or `*=`: the assignments that the Tolean subset has. -/
def AssignOp.isSimple : AssignOp → Bool
  | .assign | .add | .sub | .mul => true
  | _ => false

/-- `null`, not in parentheses. -/
def Expr.isNull : Expr → Bool
  | .null _ => true
  | _ => false

/-- The name `undefined`, not in parentheses. -/
def Expr.isUndefinedName : Expr → Bool
  | .ident _ "undefined" => true
  | _ => false

/-- A name, not in parentheses. -/
def Expr.isIdent : Expr → Bool
  | .ident .. => true
  | _ => false

/-- The name `Infinity`, not in parentheses. -/
def Expr.isInfinity : Expr → Bool
  | .ident _ "Infinity" => true
  | _ => false

/-- An array literal. -/
def Expr.isArrayLiteral : Expr → Bool
  | .array .. => true
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
  /-- `switch (disc) { … }`, with its clauses in source order. A clause is
  `case test:` or, when `test` is `none`, `default:`, with its statements. -/
  | switchStmt (span : Span) (disc : Expr) (clauses : List (Option Expr × List Stmt))

instance : Inhabited Stmt := ⟨.empty default⟩

/-- `e` is the name `n` as an assignment target, as in `n = 1` or `(n) = 1`. -/
def Expr.namesTarget (n : String) : Expr → Bool
  | .ident _ m => m == n
  | .paren _ e => e.namesTarget n
  | _ => false

mutual

/-- `e` assigns the name `n` somewhere inside it, with `=`, `+=`, `??=`,
`++` or another assignment. The cases list every constructor, so a new one
cannot be missed. -/
def Expr.assigns (n : String) : Expr → Bool
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ => false
  | .array _ es => Expr.assignsList n es
  | .object _ ps => Property.assignsList n ps
  | .paren _ e | .member _ e _ | .optMember _ e _ | .unary _ _ e => e.assigns n
  | .prefix _ _ e | .postfix _ _ e => e.namesTarget n || e.assigns n
  | .index _ a b | .binary _ _ a b => a.assigns n || b.assigns n
  | .call _ c args => c.assigns n || Expr.assignsList n args
  | .cond _ a b c => a.assigns n || b.assigns n || c.assigns n
  | .assign _ _ target value => target.namesTarget n || target.assigns n || value.assigns n
  -- The body runs only when the arrow is called; counting it anyway only
  -- refuses more.
  | .arrow _ _ _ body => body.assigns n

def Expr.assignsList (n : String) : List Expr → Bool
  | [] => false
  | e :: es => e.assigns n || Expr.assignsList n es

def Property.assignsList (n : String) : List Property → Bool
  | [] => false
  | .shorthand .. :: ps => Property.assignsList n ps
  | .keyValue _ _ v :: ps => v.assigns n || Property.assignsList n ps

end

mutual

/-- `s` assigns the name `n` somewhere inside it. -/
def Stmt.assigns (n : String) : Stmt → Bool
  | .varDecl _ d => match d.init with
    | some e => e.assigns n
    | none => false
  | .exprStmt _ e => e.assigns n
  | .returnStmt _ e => match e with
    | some e => e.assigns n
    | none => false
  | .ifStmt _ t a b => t.assigns n || a.assigns n || (match b with
    | some b => b.assigns n
    | none => false)
  | .forOfStmt _ _ _ it b => it.assigns n || b.assigns n
  | .whileStmt _ t b => t.assigns n || b.assigns n
  | .block _ ss => Stmt.assignsList n ss
  | .breakStmt _ | .continueStmt _ | .empty _ => false
  | .switchStmt _ d cs => d.assigns n || Stmt.assignsClauses n cs

def Stmt.assignsList (n : String) : List Stmt → Bool
  | [] => false
  | s :: ss => s.assigns n || Stmt.assignsList n ss

def Stmt.assignsClauses (n : String) : List (Option Expr × List Stmt) → Bool
  | [] => false
  | (t, body) :: cs => (match t with
    | some t => t.assigns n
    | none => false) || Stmt.assignsList n body || Stmt.assignsClauses n cs

end

/-- `s` declares a `const` that a statement of `rest` assigns. In JS that
assignment throws a `TypeError` (ECMA-262 §9.1.1.1.5), so the spec gives no
value for such a block, and the translator refuses it. -/
def Stmt.constAssignedIn (s : Stmt) (rest : List Stmt) : Bool :=
  match s with
  | .varDecl _ d => d.kind == .const && Stmt.assignsList d.name rest
  | _ => false

/-- Only a declaration can be a `const` that a later statement assigns. -/
@[simp] theorem Stmt.constAssignedIn_exprStmt : (Stmt.exprStmt sp e).constAssignedIn rest = false := rfl
@[simp] theorem Stmt.constAssignedIn_returnStmt : (Stmt.returnStmt sp e).constAssignedIn rest = false := rfl
@[simp] theorem Stmt.constAssignedIn_ifStmt : (Stmt.ifStmt sp t a b).constAssignedIn rest = false := rfl
@[simp] theorem Stmt.constAssignedIn_forOfStmt : (Stmt.forOfStmt sp k x it b).constAssignedIn rest = false := rfl
@[simp] theorem Stmt.constAssignedIn_whileStmt : (Stmt.whileStmt sp t b).constAssignedIn rest = false := rfl
@[simp] theorem Stmt.constAssignedIn_block : (Stmt.block sp ss).constAssignedIn rest = false := rfl
@[simp] theorem Stmt.constAssignedIn_breakStmt : (Stmt.breakStmt sp).constAssignedIn rest = false := rfl
@[simp] theorem Stmt.constAssignedIn_continueStmt : (Stmt.continueStmt sp).constAssignedIn rest = false := rfl
@[simp] theorem Stmt.constAssignedIn_empty : (Stmt.empty sp).constAssignedIn rest = false := rfl
@[simp] theorem Stmt.constAssignedIn_switchStmt : (Stmt.switchStmt sp d cs).constAssignedIn rest = false := rfl

@[simp] theorem Stmt.constAssignedIn_nil (s : Stmt) : s.constAssignedIn [] = false := by
  cases s <;> simp [Stmt.constAssignedIn, Stmt.assignsList]

/-- A clause of a `switch` declares a local at its top, outside braces. The
clauses share one scope (ECMA-262 §14.12.2, §14.12.4): such a local is in
its temporal dead zone from the start of the case block, and two clauses
may not declare the same name. -/
def clausesDeclare (clauses : List (Option Expr × List Stmt)) : Bool :=
  clauses.any fun (_, body) => body.any fun s => s matches .varDecl ..

/-- A property of an interface. -/
structure Field where
  span : Span
  readonly : Bool
  name : String
  optional : Bool
  type : TypeExpr

/-- One name of `import { a, type B } from "./x.ts"`. `typeOnly` is true for
`type B`, and for every name of `import type { … }`. -/
structure ImportName where
  span : Span
  typeOnly : Bool
  name : String
deriving DecidableEq

inductive Decl where
  /-- `import { a, b } from "source"`: named imports from another file. -/
  | «import» (span : Span) (names : List ImportName) (source : String)
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
  | .object s _ | .paren s _ | .member s _ _ | .optMember s _ _ | .index s _ _ | .call s _ _ | .unary s _ _
  | .prefix s _ _ | .postfix s _ _ | .binary s _ _ _ | .cond s _ _ _ | .assign s _ _ _
  | .arrow s _ _ _ => s

def Stmt.span : Stmt → Span
  | .varDecl s _ | .exprStmt s _ | .returnStmt s _ | .ifStmt s _ _ _ | .forOfStmt s _ _ _ _
  | .whileStmt s _ _ | .block s _ | .breakStmt s | .continueStmt s | .empty s | .switchStmt s _ _ => s

mutual

/-- `e` has no `<` or `<<` operator. -/
def Expr.lessFree : Expr → Bool
  | .binary _ op l r => op != .lt && op != .shl && l.lessFree && r.lessFree
  | .array _ es => Expr.lessFreeList es
  | .object _ ps => Property.lessFreeList ps
  | .paren _ e | .member _ e _ | .optMember _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e =>
    e.lessFree
  | .index _ a b | .assign _ _ a b => a.lessFree && b.lessFree
  | .call _ c args => c.lessFree && Expr.lessFreeList args
  | .cond _ a b c => a.lessFree && b.lessFree && c.lessFree
  -- What the parser checks after an arrow is what it checks after its body.
  | .arrow _ _ _ body => body.lessFree
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ => true

def Expr.lessFreeList : List Expr → Bool
  | [] => true
  | e :: es => e.lessFree && Expr.lessFreeList es

def Property.lessFreeList : List Property → Bool
  | [] => true
  | .shorthand .. :: ps => Property.lessFreeList ps
  | .keyValue _ _ v :: ps => v.lessFree && Property.lessFreeList ps

end

/-- A `break`. -/
def Stmt.isBreak : Stmt → Bool
  | .breakStmt _ => true
  | _ => false

def Decl.span : Decl → Span
  | .import s .. | .function s .. | .interface s .. | .typeAlias s .. | .exportedVar s _ => s
  | .stmt st => st.span

/-- `e` reads a property after a `?.`, through property reads and not
through parentheses, as `a?.b` and `a?.b.c` do. A property read of such an
`e` is a part of the same optional chain (ECMA-262 §13.3.9), so it is
skipped too where the `?.` meets `null` or `undefined`. -/
def Expr.optSpine : Expr → Bool
  | .optMember .. => true
  | .member _ o _ => o.optSpine
  | _ => false

/-- An optional chain that reads `path` from `base`, the first property after
a `?.`: `a?.b.c` reads `[b, c]` from `a`. -/
def Expr.optChain? : Expr → Option (Expr × List String)
  | .optMember _ base f => some (base, [f])
  | .member _ o f => (o.optChain?).map fun (b, fs) => (b, fs ++ [f])
  | _ => none

/-- `e` without the parentheses around it. -/
def Expr.stripParens : Expr → Expr
  | .paren _ inner => inner.stripParens
  | e => e

end tolean.TypeScript.Syntax
