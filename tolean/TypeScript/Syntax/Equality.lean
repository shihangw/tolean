import tolean.TypeScript.Syntax.Ast

/-!
Equality of syntax trees, as a function that the kernel can run.

Lean cannot derive `DecidableEq` for a type that holds lists of itself, such
as `Expr`. So `beq` compares two trees field by field, recursing on the
tree, and `beq_iff` proves that it is true exactly when the trees are equal.
A certificate uses `Module.beq` to check that the parser gives the program
that its theorems are about: the kernel runs the parser and `beq`, and
`beq_iff` turns the result into an equality.
-/
namespace tolean.TypeScript.Syntax

-- Every proof here has the same shape, so some pass a lemma that they do not use.
set_option linter.unusedSimpArgs false


mutual

def TypeExpr.beq : TypeExpr → TypeExpr → Bool
  | .keyword a0 a1, .keyword b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .null a0, .null b0 => decide (a0 = b0)
  | .literal a0 a1, .literal b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .ref a0 a1 a2, .ref b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && TypeExpr.beqList a2 b2
  | .array a0 a1, .array b0 b1 => decide (a0 = b0) && TypeExpr.beq a1 b1
  | .union a0 a1, .union b0 b1 => decide (a0 = b0) && TypeExpr.beqList a1 b1
  | .paren a0 a1, .paren b0 b1 => decide (a0 = b0) && TypeExpr.beq a1 b1
  | _, _ => false

def TypeExpr.beqList : List TypeExpr → List TypeExpr → Bool
  | [], [] => true
  | x :: xs, y :: ys => TypeExpr.beq x y && TypeExpr.beqList xs ys
  | _, _ => false

end

def TypeExpr.beqOpt : Option TypeExpr → Option TypeExpr → Bool
  | none, none => true
  | some x, some y => TypeExpr.beq x y
  | _, _ => false

mutual

theorem TypeExpr.beq_iff : (a b : TypeExpr) → TypeExpr.beq a b = true ↔ a = b
  | .keyword a0 a1, b => by
    cases b <;> simp [and_assoc, TypeExpr.beq]
  | .null a0, b => by
    cases b <;> simp [and_assoc, TypeExpr.beq]
  | .literal a0 a1, b => by
    cases b <;> simp [and_assoc, TypeExpr.beq]
  | .ref a0 a1 a2, b => by
    cases b <;> simp [and_assoc, TypeExpr.beq, TypeExpr.beqList_iff a2]
  | .array a0 a1, b => by
    cases b <;> simp [and_assoc, TypeExpr.beq, TypeExpr.beq_iff a1]
  | .union a0 a1, b => by
    cases b <;> simp [and_assoc, TypeExpr.beq, TypeExpr.beqList_iff a1]
  | .paren a0 a1, b => by
    cases b <;> simp [and_assoc, TypeExpr.beq, TypeExpr.beq_iff a1]

theorem TypeExpr.beqList_iff : (xs ys : List TypeExpr) → TypeExpr.beqList xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [and_assoc, TypeExpr.beqList]
  | x :: xs, ys => by
    cases ys <;> simp [and_assoc, TypeExpr.beqList, TypeExpr.beq_iff x, TypeExpr.beqList_iff xs]

end

theorem TypeExpr.beqOpt_iff : (o p : Option TypeExpr) → TypeExpr.beqOpt o p = true ↔ o = p
  | none, p => by cases p <;> simp [and_assoc, TypeExpr.beqOpt]
  | some x, p => by
    cases p <;> simp [and_assoc, TypeExpr.beqOpt, TypeExpr.beq_iff x]

mutual

def Expr.beq : Expr → Expr → Bool
  | .ident a0 a1, .ident b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .number a0 a1, .number b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .bigint a0 a1, .bigint b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .string a0 a1, .string b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .bool a0 a1, .bool b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .null a0, .null b0 => decide (a0 = b0)
  | .array a0 a1, .array b0 b1 => decide (a0 = b0) && Expr.beqList a1 b1
  | .object a0 a1, .object b0 b1 => decide (a0 = b0) && Property.beqList a1 b1
  | .paren a0 a1, .paren b0 b1 => decide (a0 = b0) && Expr.beq a1 b1
  | .member a0 a1 a2, .member b0 b1 b2 => decide (a0 = b0) && Expr.beq a1 b1 && decide (a2 = b2)
  | .index a0 a1 a2, .index b0 b1 b2 => decide (a0 = b0) && Expr.beq a1 b1 && Expr.beq a2 b2
  | .call a0 a1 a2, .call b0 b1 b2 => decide (a0 = b0) && Expr.beq a1 b1 && Expr.beqList a2 b2
  | .unary a0 a1 a2, .unary b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && Expr.beq a2 b2
  | .prefix a0 a1 a2, .prefix b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && Expr.beq a2 b2
  | .postfix a0 a1 a2, .postfix b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && Expr.beq a2 b2
  | .binary a0 a1 a2 a3, .binary b0 b1 b2 b3 => decide (a0 = b0) && decide (a1 = b1) && Expr.beq a2 b2 && Expr.beq a3 b3
  | .cond a0 a1 a2 a3, .cond b0 b1 b2 b3 => decide (a0 = b0) && Expr.beq a1 b1 && Expr.beq a2 b2 && Expr.beq a3 b3
  | .assign a0 a1 a2 a3, .assign b0 b1 b2 b3 => decide (a0 = b0) && decide (a1 = b1) && Expr.beq a2 b2 && Expr.beq a3 b3
  | _, _ => false

def Expr.beqList : List Expr → List Expr → Bool
  | [], [] => true
  | x :: xs, y :: ys => Expr.beq x y && Expr.beqList xs ys
  | _, _ => false

def Property.beq : Property → Property → Bool
  | .shorthand a0 a1, .shorthand b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .keyValue a0 a1 a2, .keyValue b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && Expr.beq a2 b2
  | _, _ => false

def Property.beqList : List Property → List Property → Bool
  | [], [] => true
  | x :: xs, y :: ys => Property.beq x y && Property.beqList xs ys
  | _, _ => false

end

def Expr.beqOpt : Option Expr → Option Expr → Bool
  | none, none => true
  | some x, some y => Expr.beq x y
  | _, _ => false

mutual

theorem Expr.beq_iff : (a b : Expr) → Expr.beq a b = true ↔ a = b
  | .ident a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .number a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .bigint a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .string a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .bool a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .null a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .array a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beqList_iff a1]
  | .object a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Property.beqList_iff a1]
  | .paren a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1]
  | .member a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1]
  | .index a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a2]
  | .call a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beqList_iff a2]
  | .unary a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a2]
  | .prefix a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a2]
  | .postfix a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a2]
  | .binary a0 a1 a2 a3, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a2, Expr.beq_iff a3]
  | .cond a0 a1 a2 a3, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a2, Expr.beq_iff a3]
  | .assign a0 a1 a2 a3, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a2, Expr.beq_iff a3]

theorem Expr.beqList_iff : (xs ys : List Expr) → Expr.beqList xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [and_assoc, Expr.beqList]
  | x :: xs, ys => by
    cases ys <;> simp [and_assoc, Expr.beqList, Expr.beq_iff x, Expr.beqList_iff xs]

theorem Property.beq_iff : (a b : Property) → Property.beq a b = true ↔ a = b
  | .shorthand a0 a1, b => by
    cases b <;> simp [and_assoc, Property.beq]
  | .keyValue a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Property.beq, Expr.beq_iff a2]

theorem Property.beqList_iff : (xs ys : List Property) → Property.beqList xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [and_assoc, Property.beqList]
  | x :: xs, ys => by
    cases ys <;> simp [and_assoc, Property.beqList, Property.beq_iff x, Property.beqList_iff xs]

end

theorem Expr.beqOpt_iff : (o p : Option Expr) → Expr.beqOpt o p = true ↔ o = p
  | none, p => by cases p <;> simp [and_assoc, Expr.beqOpt]
  | some x, p => by
    cases p <;> simp [and_assoc, Expr.beqOpt, Expr.beq_iff x]

def VarDecl.beq (a b : VarDecl) : Bool := decide (a.kind = b.kind) && decide (a.name = b.name) && TypeExpr.beqOpt a.type b.type && Expr.beqOpt a.init b.init

theorem VarDecl.beq_iff (a b : VarDecl) : VarDecl.beq a b = true ↔ a = b := by
  obtain ⟨kind, name, type, init⟩ := a
  cases b
  simp [and_assoc, VarDecl.beq, TypeExpr.beqOpt_iff type, Expr.beqOpt_iff init]

mutual

def Stmt.beq : Stmt → Stmt → Bool
  | .varDecl a0 a1, .varDecl b0 b1 => decide (a0 = b0) && VarDecl.beq a1 b1
  | .exprStmt a0 a1, .exprStmt b0 b1 => decide (a0 = b0) && Expr.beq a1 b1
  | .returnStmt a0 a1, .returnStmt b0 b1 => decide (a0 = b0) && Expr.beqOpt a1 b1
  | .ifStmt a0 a1 a2 a3, .ifStmt b0 b1 b2 b3 => decide (a0 = b0) && Expr.beq a1 b1 && Stmt.beq a2 b2 && Stmt.beqOpt a3 b3
  | .forOfStmt a0 a1 a2 a3 a4, .forOfStmt b0 b1 b2 b3 b4 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2) && Expr.beq a3 b3 && Stmt.beq a4 b4
  | .whileStmt a0 a1 a2, .whileStmt b0 b1 b2 => decide (a0 = b0) && Expr.beq a1 b1 && Stmt.beq a2 b2
  | .block a0 a1, .block b0 b1 => decide (a0 = b0) && Stmt.beqList a1 b1
  | .breakStmt a0, .breakStmt b0 => decide (a0 = b0)
  | .continueStmt a0, .continueStmt b0 => decide (a0 = b0)
  | .empty a0, .empty b0 => decide (a0 = b0)
  | _, _ => false

def Stmt.beqList : List Stmt → List Stmt → Bool
  | [], [] => true
  | x :: xs, y :: ys => Stmt.beq x y && Stmt.beqList xs ys
  | _, _ => false

def Stmt.beqOpt : Option Stmt → Option Stmt → Bool
  | none, none => true
  | some x, some y => Stmt.beq x y
  | _, _ => false

end

mutual

theorem Stmt.beq_iff : (a b : Stmt) → Stmt.beq a b = true ↔ a = b
  | .varDecl a0 a1, b => by
    cases b <;> simp [and_assoc, Stmt.beq, VarDecl.beq_iff a1]
  | .exprStmt a0 a1, b => by
    cases b <;> simp [and_assoc, Stmt.beq, Expr.beq_iff a1]
  | .returnStmt a0 a1, b => by
    cases b <;> simp [and_assoc, Stmt.beq, Expr.beqOpt_iff a1]
  | .ifStmt a0 a1 a2 a3, b => by
    cases b <;> simp [and_assoc, Stmt.beq, Expr.beq_iff a1, Stmt.beq_iff a2, Stmt.beqOpt_iff a3]
  | .forOfStmt a0 a1 a2 a3 a4, b => by
    cases b <;> simp [and_assoc, Stmt.beq, Expr.beq_iff a3, Stmt.beq_iff a4]
  | .whileStmt a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Stmt.beq, Expr.beq_iff a1, Stmt.beq_iff a2]
  | .block a0 a1, b => by
    cases b <;> simp [and_assoc, Stmt.beq, Stmt.beqList_iff a1]
  | .breakStmt a0, b => by
    cases b <;> simp [and_assoc, Stmt.beq]
  | .continueStmt a0, b => by
    cases b <;> simp [and_assoc, Stmt.beq]
  | .empty a0, b => by
    cases b <;> simp [and_assoc, Stmt.beq]

theorem Stmt.beqList_iff : (xs ys : List Stmt) → Stmt.beqList xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [and_assoc, Stmt.beqList]
  | x :: xs, ys => by
    cases ys <;> simp [and_assoc, Stmt.beqList, Stmt.beq_iff x, Stmt.beqList_iff xs]

theorem Stmt.beqOpt_iff : (o p : Option Stmt) → Stmt.beqOpt o p = true ↔ o = p
  | none, p => by cases p <;> simp [and_assoc, Stmt.beqOpt]
  | some x, p => by
    cases p <;> simp [and_assoc, Stmt.beqOpt, Stmt.beq_iff x]

end

def Param.beq (a b : Param) : Bool := decide (a.span = b.span) && decide (a.name = b.name) && TypeExpr.beqOpt a.type b.type

theorem Param.beq_iff (a b : Param) : Param.beq a b = true ↔ a = b := by
  obtain ⟨span, name, type⟩ := a
  cases b
  simp [and_assoc, Param.beq, TypeExpr.beqOpt_iff type]

def Param.beqList : List Param → List Param → Bool
  | [], [] => true
  | x :: xs, y :: ys => Param.beq x y && Param.beqList xs ys
  | _, _ => false

theorem Param.beqList_iff : (xs ys : List Param) → Param.beqList xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [and_assoc, Param.beqList]
  | x :: xs, ys => by
    cases ys <;> simp [and_assoc, Param.beqList, Param.beq_iff x, Param.beqList_iff xs]

def Field.beq (a b : Field) : Bool := decide (a.span = b.span) && decide (a.readonly = b.readonly) && decide (a.name = b.name) && decide (a.optional = b.optional) && TypeExpr.beq a.type b.type

theorem Field.beq_iff (a b : Field) : Field.beq a b = true ↔ a = b := by
  obtain ⟨span, readonly, name, optional, type⟩ := a
  cases b
  simp [and_assoc, Field.beq, TypeExpr.beq_iff type]

def Field.beqList : List Field → List Field → Bool
  | [], [] => true
  | x :: xs, y :: ys => Field.beq x y && Field.beqList xs ys
  | _, _ => false

theorem Field.beqList_iff : (xs ys : List Field) → Field.beqList xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [and_assoc, Field.beqList]
  | x :: xs, ys => by
    cases ys <;> simp [and_assoc, Field.beqList, Field.beq_iff x, Field.beqList_iff xs]

def Decl.beq : Decl → Decl → Bool
  | .import a0 a1 a2, .import b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .function a0 a1 a2 a3 a4 a5, .function b0 b1 b2 b3 b4 b5 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2) && Param.beqList a3 b3 && TypeExpr.beqOpt a4 b4 && Stmt.beq a5 b5
  | .interface a0 a1 a2 a3, .interface b0 b1 b2 b3 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2) && Field.beqList a3 b3
  | .typeAlias a0 a1 a2 a3, .typeAlias b0 b1 b2 b3 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2) && TypeExpr.beq a3 b3
  | .exportedVar a0 a1, .exportedVar b0 b1 => decide (a0 = b0) && VarDecl.beq a1 b1
  | .stmt a0, .stmt b0 => Stmt.beq a0 b0
  | _, _ => false

theorem Decl.beq_iff : (a b : Decl) → Decl.beq a b = true ↔ a = b
  | .import a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Decl.beq]
  | .function a0 a1 a2 a3 a4 a5, b => by
    cases b <;> simp [and_assoc, Decl.beq, Param.beqList_iff a3, TypeExpr.beqOpt_iff a4, Stmt.beq_iff a5]
  | .interface a0 a1 a2 a3, b => by
    cases b <;> simp [and_assoc, Decl.beq, Field.beqList_iff a3]
  | .typeAlias a0 a1 a2 a3, b => by
    cases b <;> simp [and_assoc, Decl.beq, TypeExpr.beq_iff a3]
  | .exportedVar a0 a1, b => by
    cases b <;> simp [and_assoc, Decl.beq, VarDecl.beq_iff a1]
  | .stmt a0, b => by
    cases b <;> simp [and_assoc, Decl.beq, Stmt.beq_iff a0]

def Decl.beqList : List Decl → List Decl → Bool
  | [], [] => true
  | x :: xs, y :: ys => Decl.beq x y && Decl.beqList xs ys
  | _, _ => false

theorem Decl.beqList_iff : (xs ys : List Decl) → Decl.beqList xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [and_assoc, Decl.beqList]
  | x :: xs, ys => by
    cases ys <;> simp [and_assoc, Decl.beqList, Decl.beq_iff x, Decl.beqList_iff xs]

def Module.beq (a b : Module) : Bool := Decl.beqList a.decls b.decls

theorem Module.beq_iff (a b : Module) : Module.beq a b = true ↔ a = b := by
  obtain ⟨decls⟩ := a
  cases b
  simp [and_assoc, Module.beq, Decl.beqList_iff decls]

end tolean.TypeScript.Syntax
