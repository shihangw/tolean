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
  /-- `[A, B]`, or `readonly [A, B]` when `readonly` is true: a tuple type. -/
  | tuple (span : Span) (readonly : Bool) (elems : List TypeExpr)

/-- A parameter of a function or an arrow function. An optional parameter,
`x?: T`, is `undefined` when a call leaves it out. -/
structure Param where
  span : Span
  name : String
  optional : Bool := false
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
  /-- `expr as const`. Type stripping removes `as const`, so it has the value
  of `expr`. -/
  | asConst (span : Span) (expr : Expr)
  /-- `expr satisfies type`. Type stripping removes `satisfies type`, so it has
  the value of `expr`. -/
  | satisfies (span : Span) (expr : Expr) (type : TypeExpr)
  /-- `new C<A, B>(args)`, where `C` is a name. The type arguments may be
  absent, and the arguments are always in parentheses. -/
  | new (span : Span) (callee : String) (typeArgs : List TypeExpr) (args : List Expr)

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
  /-- `for (init; test; update) body`, the counted loop. Each of the three
  parts may be absent. -/
  | forStmt (span : Span) (init : Option VarDecl) (test : Option Expr) (update : Option Expr) (body : Stmt)
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
  | .asConst _ e | .satisfies _ e _ => e.assigns n
  | .new _ _ _ args => Expr.assignsList n args

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
  | .forStmt _ init t u b => (match init with
    | some { init := some e, .. } => e.assigns n
    | _ => false) || (match t with
    | some t => t.assigns n
    | none => false) || (match u with
    | some u => u.assigns n
    | none => false) || b.assigns n
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

/-- The methods that change the array, map or set that they are called on. -/
def changingMethods : List String := ["push", "set", "add", "delete"]

mutual

/-- `e` calls a method that changes the array, map or set that the name `n`
holds, such as `n.push(x)` or `n.delete(k)`, somewhere inside it. -/
def Expr.mutates (n : String) : Expr → Bool
  | .call _ (.member _ (.ident _ m) method) args =>
    (m == n && changingMethods.contains method) || Expr.mutatesList n args
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ => false
  | .array _ es => Expr.mutatesList n es
  | .object _ ps => Property.mutatesList n ps
  | .paren _ e | .member _ e _ | .optMember _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e =>
    e.mutates n
  | .index _ a b | .binary _ _ a b | .assign _ _ a b => a.mutates n || b.mutates n
  | .call _ c args => c.mutates n || Expr.mutatesList n args
  | .cond _ a b c => a.mutates n || b.mutates n || c.mutates n
  | .arrow _ _ _ body => body.mutates n
  | .asConst _ e | .satisfies _ e _ => e.mutates n
  | .new _ _ _ args => Expr.mutatesList n args

def Expr.mutatesList (n : String) : List Expr → Bool
  | [] => false
  | e :: es => e.mutates n || Expr.mutatesList n es

def Property.mutatesList (n : String) : List Property → Bool
  | [] => false
  | .shorthand .. :: ps => Property.mutatesList n ps
  | .keyValue _ _ v :: ps => v.mutates n || Property.mutatesList n ps

end

mutual

/-- `s` changes the array, map or set that the name `n` holds somewhere
inside it, as `Expr.mutates` says. -/
def Stmt.mutates (n : String) : Stmt → Bool
  | .varDecl _ d => match d.init with
    | some e => e.mutates n
    | none => false
  | .exprStmt _ e => e.mutates n
  | .returnStmt _ e => match e with
    | some e => e.mutates n
    | none => false
  | .ifStmt _ t a b => t.mutates n || a.mutates n || (match b with
    | some b => b.mutates n
    | none => false)
  | .forOfStmt _ _ _ it b => it.mutates n || b.mutates n
  | .forStmt _ init t u b => (match init with
    | some { init := some e, .. } => e.mutates n
    | _ => false) || (match t with
    | some t => t.mutates n
    | none => false) || (match u with
    | some u => u.mutates n
    | none => false) || b.mutates n
  | .whileStmt _ t b => t.mutates n || b.mutates n
  | .block _ ss => Stmt.mutatesList n ss
  | .breakStmt _ | .continueStmt _ | .empty _ => false
  | .switchStmt _ d cs => d.mutates n || Stmt.mutatesClauses n cs

def Stmt.mutatesList (n : String) : List Stmt → Bool
  | [] => false
  | s :: ss => s.mutates n || Stmt.mutatesList n ss

def Stmt.mutatesClauses (n : String) : List (Option Expr × List Stmt) → Bool
  | [] => false
  | (t, body) :: cs => (match t with
    | some t => t.mutates n
    | none => false) || Stmt.mutatesList n body || Stmt.mutatesClauses n cs

end

mutual

/-- `e` mentions a name that `p` holds for, outside the arguments of a `new`.
A `new Map(m)` or `new Set(xs)` copies its argument, so its value is a new
collection that no name holds. Any other expression may give the collection
of a name it mentions, such as `(s)`, `s satisfies T`, `c ? s : t` or `f(s)`. -/
def Expr.mayHold (p : String → Bool) : Expr → Bool
  | .ident _ n => p n
  | .number .. | .bigint .. | .string .. | .bool .. | .null _ | .new .. => false
  | .array _ es => Expr.mayHoldList p es
  | .object _ ps => Property.mayHoldList p ps
  | .paren _ e | .member _ e _ | .optMember _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e =>
    e.mayHold p
  | .index _ a b | .binary _ _ a b | .assign _ _ a b => a.mayHold p || b.mayHold p
  | .call _ c args => c.mayHold p || Expr.mayHoldList p args
  | .cond _ a b c => a.mayHold p || b.mayHold p || c.mayHold p
  | .arrow _ _ _ body => body.mayHold p
  | .asConst _ e | .satisfies _ e _ => e.mayHold p

def Expr.mayHoldList (p : String → Bool) : List Expr → Bool
  | [] => false
  | e :: es => e.mayHold p || Expr.mayHoldList p es

def Property.mayHoldList (p : String → Bool) : List Property → Bool
  | [] => false
  | .shorthand _ n :: ps => p n || Property.mayHoldList p ps
  | .keyValue _ _ v :: ps => v.mayHold p || Property.mayHoldList p ps

end

/-- The body of `for (… of iterable)` may change what the loop runs over: it
changes the array, map or set of a name that `iterable` may give. A JS loop
sees such a change while it runs. The test is conservative: it does not need
to know which name, if any, the iterable gives at run time. -/
def Stmt.mutatesIterable (iterable : Expr) (body : Stmt) : Bool :=
  iterable.mayHold body.mutates

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
@[simp] theorem Stmt.constAssignedIn_forStmt : (Stmt.forStmt sp i t u b).constAssignedIn rest = false := rfl
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

/-- A member of a string enum: `Name = "value"`. -/
structure EnumMember where
  span : Span
  name : String
  value : String
deriving DecidableEq

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
  /-- `export { a, type B }`, which exports declarations of the file, or
  `export { a } from "source"`, which exports names of another file. -/
  | exports (span : Span) (names : List ImportName) (source : Option String)
  /-- `body` is a `block`. `typeParams` are the names in `<A, B>` after the
  name of a generic function. -/
  | function (span : Span) (exported : Bool) (name : String) (typeParams : List String) (params : List Param)
      (returnType : Option TypeExpr) (body : Stmt)
  /-- `typeParams` are the names in `<A, B>` after the name of a generic
  interface, as for a type alias and a function. -/
  | interface (span : Span) (exported : Bool) (name : String) (typeParams : List String) (fields : List Field)
  | typeAlias (span : Span) (exported : Bool) (name : String) (typeParams : List String) (type : TypeExpr)
  /-- `enum Name { A = "a", B = "b" }`: an enum whose members are strings. -/
  | enum (span : Span) (exported : Bool) (name : String) (members : List EnumMember)
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
  | .keyword s _ | .null s | .literal s _ | .ref s _ _ | .array s _ | .union s _ | .paren s _
  | .tuple s _ _ => s

def Expr.span : Expr → Span
  | .ident s _ | .number s _ | .bigint s _ | .string s _ | .bool s _ | .null s | .array s _
  | .object s _ | .paren s _ | .member s _ _ | .optMember s _ _ | .index s _ _ | .call s _ _ | .unary s _ _
  | .prefix s _ _ | .postfix s _ _ | .binary s _ _ _ | .cond s _ _ _ | .assign s _ _ _
  | .arrow s _ _ _ | .asConst s _ | .satisfies s _ _ | .new s _ _ _ => s

def Stmt.span : Stmt → Span
  | .varDecl s _ | .exprStmt s _ | .returnStmt s _ | .ifStmt s _ _ _ | .forOfStmt s _ _ _ _
  | .forStmt s _ _ _ _ | .whileStmt s _ _ | .block s _ | .breakStmt s | .continueStmt s | .empty s | .switchStmt s _ _ => s

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
  -- A `<` in the type reads type arguments, which the parser checks itself.
  | .asConst _ e | .satisfies _ e _ => e.lessFree
  -- The type arguments are a group that the parser reads itself.
  | .new _ _ _ args => Expr.lessFreeList args
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ => true

def Expr.lessFreeList : List Expr → Bool
  | [] => true
  | e :: es => e.lessFree && Expr.lessFreeList es

def Property.lessFreeList : List Property → Bool
  | [] => true
  | .shorthand .. :: ps => Property.lessFreeList ps
  | .keyValue _ _ v :: ps => v.lessFree && Property.lessFreeList ps

end

mutual

/-- `e` has no `in` operator outside parentheses, `{ … }`, the arguments of a
call, an index and the middle of a conditional. ECMA-262 reads the
declaration at the start of a counted `for` this way (§14.7.4, the `[~In]`
parameter), so that an `in` after the declaration starts a `for … in` loop.
ECMA-262 also allows an `in` inside `[ … ]` there, but `tsc` does not, so
`e` has none there either. -/
def Expr.inFree : Expr → Bool
  | .binary _ op l r => op != .«in» && l.inFree && r.inFree
  | .cond _ test _ ifFalse => test.inFree && ifFalse.inFree
  | .assign _ _ target value => target.inFree && value.inFree
  | .array _ es => Expr.inFreeList es
  | .member _ e _ | .optMember _ e _ | .index _ e _ | .call _ e _ | .unary _ _ e | .prefix _ _ e
  | .postfix _ _ e | .arrow _ _ _ e | .asConst _ e | .satisfies _ e _ => e.inFree
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ | .object .. | .paren ..
  | .new .. => true

def Expr.inFreeList : List Expr → Bool
  | [] => true
  | e :: es => e.inFree && Expr.inFreeList es

end

/-- The value of `d` has no `in` where `Expr.inFree` finds one. -/
def VarDecl.inFree (d : VarDecl) : Bool :=
  match d.init with
  | some e => e.inFree
  | none => true

/-- A `break`. -/
def Stmt.isBreak : Stmt → Bool
  | .breakStmt _ => true
  | _ => false

def Decl.span : Decl → Span
  | .import s .. | .exports s .. | .function s .. | .interface s .. | .typeAlias s .. | .enum s .. | .exportedVar s _ => s
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
