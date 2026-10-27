-- Certificate written by tolean for access/rbac.ts. Do not edit.
import tolean.TypeScript.Spec.Lemmas.Eval
import access.Rbac

namespace access.RbacCert

open tolean.TypeScript tolean.TypeScript.Eval

-- The proofs pass the same lemmas everywhere, so some go unused.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The program, as the parser read it. -/
def program : tolean.TypeScript.Syntax.Module :=
  { decls := [
  (tolean.TypeScript.Syntax.Decl.interface (sp 3 1 7 2) true "Binding" [{ span := (sp 4 3 4 27), readonly := true, name := "tenant", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 4 20 4 26) "string") }, { span := (sp 5 3 5 25), readonly := true, name := "role", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 5 18 5 24) "string") }, { span := (sp 6 3 6 27), readonly := true, name := "member", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 6 20 6 26) "string") }]),
  (tolean.TypeScript.Syntax.Decl.interface (sp 10 1 13 2) true "Grant" [{ span := (sp 11 3 11 25), readonly := true, name := "role", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 11 18 11 24) "string") }, { span := (sp 12 3 12 31), readonly := true, name := "permission", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 12 24 12 30) "string") }]),
  (tolean.TypeScript.Syntax.Decl.interface (sp 16 1 19 2) true "Membership" [{ span := (sp 17 3 17 26), readonly := true, name := "group", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 17 19 17 25) "string") }, { span := (sp 18 3 18 30), readonly := true, name := "principal", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 18 23 18 29) "string") }]),
  (tolean.TypeScript.Syntax.Decl.interface (sp 22 1 26 2) true "Deny" [{ span := (sp 23 3 23 27), readonly := true, name := "tenant", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 23 20 23 26) "string") }, { span := (sp 24 3 24 31), readonly := true, name := "permission", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 24 24 24 30) "string") }, { span := (sp 25 3 25 27), readonly := true, name := "member", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 25 20 25 26) "string") }]),
  (tolean.TypeScript.Syntax.Decl.interface (sp 28 1 33 2) true "Policy" [{ span := (sp 29 3 29 45), readonly := true, name := "bindings", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.ref (sp 29 22 29 44) "ReadonlyArray" [(tolean.TypeScript.Syntax.TypeExpr.ref (sp 29 36 29 43) "Binding" [])]) }, { span := (sp 30 3 30 41), readonly := true, name := "grants", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.ref (sp 30 20 30 40) "ReadonlyArray" [(tolean.TypeScript.Syntax.TypeExpr.ref (sp 30 34 30 39) "Grant" [])]) }, { span := (sp 31 3 31 46), readonly := true, name := "groups", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.ref (sp 31 20 31 45) "ReadonlyArray" [(tolean.TypeScript.Syntax.TypeExpr.ref (sp 31 34 31 44) "Membership" [])]) }, { span := (sp 32 3 32 40), readonly := true, name := "denies", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.ref (sp 32 20 32 39) "ReadonlyArray" [(tolean.TypeScript.Syntax.TypeExpr.ref (sp 32 34 32 38) "Deny" [])]) }]),
  (tolean.TypeScript.Syntax.Decl.interface (sp 36 1 40 2) true "Request" [{ span := (sp 37 3 37 27), readonly := true, name := "tenant", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 37 20 37 26) "string") }, { span := (sp 38 3 38 30), readonly := true, name := "principal", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 38 23 38 29) "string") }, { span := (sp 39 3 39 31), readonly := true, name := "permission", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 39 24 39 30) "string") }]),
  (tolean.TypeScript.Syntax.Decl.function (sp 42 1 50 2) true "inGroup" [{ span := (sp 42 25 42 58), name := "groups", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 42 33 42 58) "ReadonlyArray" [(tolean.TypeScript.Syntax.TypeExpr.ref (sp 42 47 42 57) "Membership" [])])) }, { span := (sp 42 60 42 73), name := "group", type := (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 42 67 42 73) "string")) }, { span := (sp 42 75 42 92), name := "principal", type := (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 42 86 42 92) "string")) }] (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 42 95 42 102) "boolean"))
    (tolean.TypeScript.Syntax.Stmt.block (sp 42 103 50 2) [(tolean.TypeScript.Syntax.Stmt.varDecl (sp 43 3 43 21) { kind := tolean.TypeScript.Syntax.VarKind.«let», name := "found", type := none, init := (some (tolean.TypeScript.Syntax.Expr.bool (sp 43 15 43 20) false)) }), (tolean.TypeScript.Syntax.Stmt.forOfStmt (sp 44 3 48 4) tolean.TypeScript.Syntax.VarKind.const "m" (tolean.TypeScript.Syntax.Expr.ident (sp 44 19 44 25) "groups") (tolean.TypeScript.Syntax.Stmt.block (sp 44 27 48 4) [(tolean.TypeScript.Syntax.Stmt.ifStmt (sp 45 5 47 6) (tolean.TypeScript.Syntax.Expr.binary (sp 45 9 45 55) tolean.TypeScript.Syntax.BinOp.and (tolean.TypeScript.Syntax.Expr.binary (sp 45 9 45 26) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.member (sp 45 9 45 16) (tolean.TypeScript.Syntax.Expr.ident (sp 45 9 45 10) "m") "group") (tolean.TypeScript.Syntax.Expr.ident (sp 45 21 45 26) "group")) (tolean.TypeScript.Syntax.Expr.binary (sp 45 30 45 55) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.member (sp 45 30 45 41) (tolean.TypeScript.Syntax.Expr.ident (sp 45 30 45 31) "m") "principal") (tolean.TypeScript.Syntax.Expr.ident (sp 45 46 45 55) "principal"))) (tolean.TypeScript.Syntax.Stmt.block (sp 45 57 47 6) [(tolean.TypeScript.Syntax.Stmt.exprStmt (sp 46 7 46 20) (tolean.TypeScript.Syntax.Expr.assign (sp 46 7 46 19) tolean.TypeScript.Syntax.AssignOp.assign (tolean.TypeScript.Syntax.Expr.ident (sp 46 7 46 12) "found") (tolean.TypeScript.Syntax.Expr.bool (sp 46 15 46 19) true)))]) none)])), (tolean.TypeScript.Syntax.Stmt.returnStmt (sp 49 3 49 16) (some (tolean.TypeScript.Syntax.Expr.ident (sp 49 10 49 15) "found")))])),
  (tolean.TypeScript.Syntax.Decl.function (sp 53 1 55 2) true "isMember" [{ span := (sp 53 26 53 59), name := "groups", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 53 34 53 59) "ReadonlyArray" [(tolean.TypeScript.Syntax.TypeExpr.ref (sp 53 48 53 58) "Membership" [])])) }, { span := (sp 53 61 53 75), name := "member", type := (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 53 69 53 75) "string")) }, { span := (sp 53 77 53 94), name := "principal", type := (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 53 88 53 94) "string")) }] (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 53 97 53 104) "boolean"))
    (tolean.TypeScript.Syntax.Stmt.block (sp 53 105 55 2) [(tolean.TypeScript.Syntax.Stmt.returnStmt (sp 54 3 54 69) (some (tolean.TypeScript.Syntax.Expr.binary (sp 54 10 54 68) tolean.TypeScript.Syntax.BinOp.or (tolean.TypeScript.Syntax.Expr.binary (sp 54 10 54 30) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.ident (sp 54 10 54 16) "member") (tolean.TypeScript.Syntax.Expr.ident (sp 54 21 54 30) "principal")) (tolean.TypeScript.Syntax.Expr.call (sp 54 34 54 68) (tolean.TypeScript.Syntax.Expr.ident (sp 54 34 54 41) "inGroup") [(tolean.TypeScript.Syntax.Expr.ident (sp 54 42 54 48) "groups"), (tolean.TypeScript.Syntax.Expr.ident (sp 54 50 54 56) "member"), (tolean.TypeScript.Syntax.Expr.ident (sp 54 58 54 67) "principal")]))))])),
  (tolean.TypeScript.Syntax.Decl.function (sp 57 1 65 2) true "roleGrants" [{ span := (sp 57 28 57 56), name := "grants", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 57 36 57 56) "ReadonlyArray" [(tolean.TypeScript.Syntax.TypeExpr.ref (sp 57 50 57 55) "Grant" [])])) }, { span := (sp 57 58 57 70), name := "role", type := (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 57 64 57 70) "string")) }, { span := (sp 57 72 57 90), name := "permission", type := (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 57 84 57 90) "string")) }] (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 57 93 57 100) "boolean"))
    (tolean.TypeScript.Syntax.Stmt.block (sp 57 101 65 2) [(tolean.TypeScript.Syntax.Stmt.varDecl (sp 58 3 58 21) { kind := tolean.TypeScript.Syntax.VarKind.«let», name := "found", type := none, init := (some (tolean.TypeScript.Syntax.Expr.bool (sp 58 15 58 20) false)) }), (tolean.TypeScript.Syntax.Stmt.forOfStmt (sp 59 3 63 4) tolean.TypeScript.Syntax.VarKind.const "g" (tolean.TypeScript.Syntax.Expr.ident (sp 59 19 59 25) "grants") (tolean.TypeScript.Syntax.Stmt.block (sp 59 27 63 4) [(tolean.TypeScript.Syntax.Stmt.ifStmt (sp 60 5 62 6) (tolean.TypeScript.Syntax.Expr.binary (sp 60 9 60 55) tolean.TypeScript.Syntax.BinOp.and (tolean.TypeScript.Syntax.Expr.binary (sp 60 9 60 24) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.member (sp 60 9 60 15) (tolean.TypeScript.Syntax.Expr.ident (sp 60 9 60 10) "g") "role") (tolean.TypeScript.Syntax.Expr.ident (sp 60 20 60 24) "role")) (tolean.TypeScript.Syntax.Expr.binary (sp 60 28 60 55) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.member (sp 60 28 60 40) (tolean.TypeScript.Syntax.Expr.ident (sp 60 28 60 29) "g") "permission") (tolean.TypeScript.Syntax.Expr.ident (sp 60 45 60 55) "permission"))) (tolean.TypeScript.Syntax.Stmt.block (sp 60 57 62 6) [(tolean.TypeScript.Syntax.Stmt.exprStmt (sp 61 7 61 20) (tolean.TypeScript.Syntax.Expr.assign (sp 61 7 61 19) tolean.TypeScript.Syntax.AssignOp.assign (tolean.TypeScript.Syntax.Expr.ident (sp 61 7 61 12) "found") (tolean.TypeScript.Syntax.Expr.bool (sp 61 15 61 19) true)))]) none)])), (tolean.TypeScript.Syntax.Stmt.returnStmt (sp 64 3 64 16) (some (tolean.TypeScript.Syntax.Expr.ident (sp 64 10 64 15) "found")))])),
  (tolean.TypeScript.Syntax.Decl.function (sp 67 1 70 2) true "bindingAllows" [{ span := (sp 67 31 67 40), name := "p", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 67 34 67 40) "Policy" [])) }, { span := (sp 67 42 67 52), name := "b", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 67 45 67 52) "Binding" [])) }, { span := (sp 67 54 67 66), name := "req", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 67 59 67 66) "Request" [])) }] (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 67 69 67 76) "boolean"))
    (tolean.TypeScript.Syntax.Stmt.block (sp 67 77 70 2) [(tolean.TypeScript.Syntax.Stmt.returnStmt (sp 68 3 69 50) (some (tolean.TypeScript.Syntax.Expr.binary (sp 68 10 69 49) tolean.TypeScript.Syntax.BinOp.and (tolean.TypeScript.Syntax.Expr.binary (sp 68 10 68 80) tolean.TypeScript.Syntax.BinOp.and (tolean.TypeScript.Syntax.Expr.binary (sp 68 10 68 33) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.member (sp 68 10 68 18) (tolean.TypeScript.Syntax.Expr.ident (sp 68 10 68 11) "b") "tenant") (tolean.TypeScript.Syntax.Expr.member (sp 68 23 68 33) (tolean.TypeScript.Syntax.Expr.ident (sp 68 23 68 26) "req") "tenant")) (tolean.TypeScript.Syntax.Expr.call (sp 68 37 68 80) (tolean.TypeScript.Syntax.Expr.ident (sp 68 37 68 45) "isMember") [(tolean.TypeScript.Syntax.Expr.member (sp 68 46 68 54) (tolean.TypeScript.Syntax.Expr.ident (sp 68 46 68 47) "p") "groups"), (tolean.TypeScript.Syntax.Expr.member (sp 68 56 68 64) (tolean.TypeScript.Syntax.Expr.ident (sp 68 56 68 57) "b") "member"), (tolean.TypeScript.Syntax.Expr.member (sp 68 66 68 79) (tolean.TypeScript.Syntax.Expr.ident (sp 68 66 68 69) "req") "principal")])) (tolean.TypeScript.Syntax.Expr.call (sp 69 5 69 49) (tolean.TypeScript.Syntax.Expr.ident (sp 69 5 69 15) "roleGrants") [(tolean.TypeScript.Syntax.Expr.member (sp 69 16 69 24) (tolean.TypeScript.Syntax.Expr.ident (sp 69 16 69 17) "p") "grants"), (tolean.TypeScript.Syntax.Expr.member (sp 69 26 69 32) (tolean.TypeScript.Syntax.Expr.ident (sp 69 26 69 27) "b") "role"), (tolean.TypeScript.Syntax.Expr.member (sp 69 34 69 48) (tolean.TypeScript.Syntax.Expr.ident (sp 69 34 69 37) "req") "permission")]))))])),
  (tolean.TypeScript.Syntax.Decl.function (sp 72 1 75 2) true "denyApplies" [{ span := (sp 72 29 72 38), name := "p", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 72 32 72 38) "Policy" [])) }, { span := (sp 72 40 72 47), name := "d", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 72 43 72 47) "Deny" [])) }, { span := (sp 72 49 72 61), name := "req", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 72 54 72 61) "Request" [])) }] (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 72 64 72 71) "boolean"))
    (tolean.TypeScript.Syntax.Stmt.block (sp 72 72 75 2) [(tolean.TypeScript.Syntax.Stmt.returnStmt (sp 73 3 74 49) (some (tolean.TypeScript.Syntax.Expr.binary (sp 73 10 74 48) tolean.TypeScript.Syntax.BinOp.and (tolean.TypeScript.Syntax.Expr.binary (sp 73 10 73 68) tolean.TypeScript.Syntax.BinOp.and (tolean.TypeScript.Syntax.Expr.binary (sp 73 10 73 33) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.member (sp 73 10 73 18) (tolean.TypeScript.Syntax.Expr.ident (sp 73 10 73 11) "d") "tenant") (tolean.TypeScript.Syntax.Expr.member (sp 73 23 73 33) (tolean.TypeScript.Syntax.Expr.ident (sp 73 23 73 26) "req") "tenant")) (tolean.TypeScript.Syntax.Expr.binary (sp 73 37 73 68) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.member (sp 73 37 73 49) (tolean.TypeScript.Syntax.Expr.ident (sp 73 37 73 38) "d") "permission") (tolean.TypeScript.Syntax.Expr.member (sp 73 54 73 68) (tolean.TypeScript.Syntax.Expr.ident (sp 73 54 73 57) "req") "permission"))) (tolean.TypeScript.Syntax.Expr.call (sp 74 5 74 48) (tolean.TypeScript.Syntax.Expr.ident (sp 74 5 74 13) "isMember") [(tolean.TypeScript.Syntax.Expr.member (sp 74 14 74 22) (tolean.TypeScript.Syntax.Expr.ident (sp 74 14 74 15) "p") "groups"), (tolean.TypeScript.Syntax.Expr.member (sp 74 24 74 32) (tolean.TypeScript.Syntax.Expr.ident (sp 74 24 74 25) "d") "member"), (tolean.TypeScript.Syntax.Expr.member (sp 74 34 74 47) (tolean.TypeScript.Syntax.Expr.ident (sp 74 34 74 37) "req") "principal")]))))])),
  (tolean.TypeScript.Syntax.Decl.function (sp 77 1 85 2) true "allowed" [{ span := (sp 77 25 77 34), name := "p", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 77 28 77 34) "Policy" [])) }, { span := (sp 77 36 77 48), name := "req", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 77 41 77 48) "Request" [])) }] (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 77 51 77 58) "boolean"))
    (tolean.TypeScript.Syntax.Stmt.block (sp 77 59 85 2) [(tolean.TypeScript.Syntax.Stmt.varDecl (sp 78 3 78 21) { kind := tolean.TypeScript.Syntax.VarKind.«let», name := "found", type := none, init := (some (tolean.TypeScript.Syntax.Expr.bool (sp 78 15 78 20) false)) }), (tolean.TypeScript.Syntax.Stmt.forOfStmt (sp 79 3 83 4) tolean.TypeScript.Syntax.VarKind.const "b" (tolean.TypeScript.Syntax.Expr.member (sp 79 19 79 29) (tolean.TypeScript.Syntax.Expr.ident (sp 79 19 79 20) "p") "bindings") (tolean.TypeScript.Syntax.Stmt.block (sp 79 31 83 4) [(tolean.TypeScript.Syntax.Stmt.ifStmt (sp 80 5 82 6) (tolean.TypeScript.Syntax.Expr.call (sp 80 9 80 33) (tolean.TypeScript.Syntax.Expr.ident (sp 80 9 80 22) "bindingAllows") [(tolean.TypeScript.Syntax.Expr.ident (sp 80 23 80 24) "p"), (tolean.TypeScript.Syntax.Expr.ident (sp 80 26 80 27) "b"), (tolean.TypeScript.Syntax.Expr.ident (sp 80 29 80 32) "req")]) (tolean.TypeScript.Syntax.Stmt.block (sp 80 35 82 6) [(tolean.TypeScript.Syntax.Stmt.exprStmt (sp 81 7 81 20) (tolean.TypeScript.Syntax.Expr.assign (sp 81 7 81 19) tolean.TypeScript.Syntax.AssignOp.assign (tolean.TypeScript.Syntax.Expr.ident (sp 81 7 81 12) "found") (tolean.TypeScript.Syntax.Expr.bool (sp 81 15 81 19) true)))]) none)])), (tolean.TypeScript.Syntax.Stmt.returnStmt (sp 84 3 84 16) (some (tolean.TypeScript.Syntax.Expr.ident (sp 84 10 84 15) "found")))])),
  (tolean.TypeScript.Syntax.Decl.function (sp 87 1 95 2) true "denied" [{ span := (sp 87 24 87 33), name := "p", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 87 27 87 33) "Policy" [])) }, { span := (sp 87 35 87 47), name := "req", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 87 40 87 47) "Request" [])) }] (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 87 50 87 57) "boolean"))
    (tolean.TypeScript.Syntax.Stmt.block (sp 87 58 95 2) [(tolean.TypeScript.Syntax.Stmt.varDecl (sp 88 3 88 21) { kind := tolean.TypeScript.Syntax.VarKind.«let», name := "found", type := none, init := (some (tolean.TypeScript.Syntax.Expr.bool (sp 88 15 88 20) false)) }), (tolean.TypeScript.Syntax.Stmt.forOfStmt (sp 89 3 93 4) tolean.TypeScript.Syntax.VarKind.const "d" (tolean.TypeScript.Syntax.Expr.member (sp 89 19 89 27) (tolean.TypeScript.Syntax.Expr.ident (sp 89 19 89 20) "p") "denies") (tolean.TypeScript.Syntax.Stmt.block (sp 89 29 93 4) [(tolean.TypeScript.Syntax.Stmt.ifStmt (sp 90 5 92 6) (tolean.TypeScript.Syntax.Expr.call (sp 90 9 90 31) (tolean.TypeScript.Syntax.Expr.ident (sp 90 9 90 20) "denyApplies") [(tolean.TypeScript.Syntax.Expr.ident (sp 90 21 90 22) "p"), (tolean.TypeScript.Syntax.Expr.ident (sp 90 24 90 25) "d"), (tolean.TypeScript.Syntax.Expr.ident (sp 90 27 90 30) "req")]) (tolean.TypeScript.Syntax.Stmt.block (sp 90 33 92 6) [(tolean.TypeScript.Syntax.Stmt.exprStmt (sp 91 7 91 20) (tolean.TypeScript.Syntax.Expr.assign (sp 91 7 91 19) tolean.TypeScript.Syntax.AssignOp.assign (tolean.TypeScript.Syntax.Expr.ident (sp 91 7 91 12) "found") (tolean.TypeScript.Syntax.Expr.bool (sp 91 15 91 19) true)))]) none)])), (tolean.TypeScript.Syntax.Stmt.returnStmt (sp 94 3 94 16) (some (tolean.TypeScript.Syntax.Expr.ident (sp 94 10 94 15) "found")))])),
  (tolean.TypeScript.Syntax.Decl.function (sp 98 1 100 2) true "permits" [{ span := (sp 98 25 98 34), name := "p", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 98 28 98 34) "Policy" [])) }, { span := (sp 98 36 98 48), name := "req", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 98 41 98 48) "Request" [])) }] (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 98 51 98 58) "boolean"))
    (tolean.TypeScript.Syntax.Stmt.block (sp 98 59 100 2) [(tolean.TypeScript.Syntax.Stmt.returnStmt (sp 99 3 99 45) (some (tolean.TypeScript.Syntax.Expr.binary (sp 99 10 99 44) tolean.TypeScript.Syntax.BinOp.and (tolean.TypeScript.Syntax.Expr.call (sp 99 10 99 25) (tolean.TypeScript.Syntax.Expr.ident (sp 99 10 99 17) "allowed") [(tolean.TypeScript.Syntax.Expr.ident (sp 99 18 99 19) "p"), (tolean.TypeScript.Syntax.Expr.ident (sp 99 21 99 24) "req")]) (tolean.TypeScript.Syntax.Expr.unary (sp 99 29 99 44) tolean.TypeScript.Syntax.UnaryOp.not (tolean.TypeScript.Syntax.Expr.call (sp 99 30 99 44) (tolean.TypeScript.Syntax.Expr.ident (sp 99 30 99 36) "denied") [(tolean.TypeScript.Syntax.Expr.ident (sp 99 37 99 38) "p"), (tolean.TypeScript.Syntax.Expr.ident (sp 99 40 99 43) "req")])))))]))] }

def encodeBinding {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Binding) : Val N := Val.obj [("tenant", Val.str x.tenant), ("role", Val.str x.role), ("member", Val.str x.member)]

def decodeBinding {N : Type} [tolean.TypeScript.JSNumber N] : Option (Val N) → access.Rbac.Binding
  | some (.obj fs) => { tenant := decStr (fs.lookup "tenant"), role := decStr (fs.lookup "role"), member := decStr (fs.lookup "member") }
  | _ => { tenant := decStr (none : Option (Val N)), role := decStr (none : Option (Val N)), member := decStr (none : Option (Val N)) }

@[simp] theorem decodeBinding_encodeBinding {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Binding) : decodeBinding (some (encodeBinding (N := N) x)) = x := by
  cases x; simp [decodeBinding, encodeBinding, List.lookup, encList, encNull]

def encodeGrant {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Grant) : Val N := Val.obj [("role", Val.str x.role), ("permission", Val.str x.permission)]

def decodeGrant {N : Type} [tolean.TypeScript.JSNumber N] : Option (Val N) → access.Rbac.Grant
  | some (.obj fs) => { role := decStr (fs.lookup "role"), permission := decStr (fs.lookup "permission") }
  | _ => { role := decStr (none : Option (Val N)), permission := decStr (none : Option (Val N)) }

@[simp] theorem decodeGrant_encodeGrant {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Grant) : decodeGrant (some (encodeGrant (N := N) x)) = x := by
  cases x; simp [decodeGrant, encodeGrant, List.lookup, encList, encNull]

def encodeMembership {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Membership) : Val N := Val.obj [("group", Val.str x.group), ("principal", Val.str x.principal)]

def decodeMembership {N : Type} [tolean.TypeScript.JSNumber N] : Option (Val N) → access.Rbac.Membership
  | some (.obj fs) => { group := decStr (fs.lookup "group"), principal := decStr (fs.lookup "principal") }
  | _ => { group := decStr (none : Option (Val N)), principal := decStr (none : Option (Val N)) }

@[simp] theorem decodeMembership_encodeMembership {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Membership) : decodeMembership (some (encodeMembership (N := N) x)) = x := by
  cases x; simp [decodeMembership, encodeMembership, List.lookup, encList, encNull]

def encodeDeny {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Deny) : Val N := Val.obj [("tenant", Val.str x.tenant), ("permission", Val.str x.permission), ("member", Val.str x.member)]

def decodeDeny {N : Type} [tolean.TypeScript.JSNumber N] : Option (Val N) → access.Rbac.Deny
  | some (.obj fs) => { tenant := decStr (fs.lookup "tenant"), permission := decStr (fs.lookup "permission"), member := decStr (fs.lookup "member") }
  | _ => { tenant := decStr (none : Option (Val N)), permission := decStr (none : Option (Val N)), member := decStr (none : Option (Val N)) }

@[simp] theorem decodeDeny_encodeDeny {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Deny) : decodeDeny (some (encodeDeny (N := N) x)) = x := by
  cases x; simp [decodeDeny, encodeDeny, List.lookup, encList, encNull]

def encodePolicy {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Policy) : Val N := Val.obj [("bindings", (encList encodeBinding) x.bindings), ("grants", (encList encodeGrant) x.grants), ("groups", (encList encodeMembership) x.groups), ("denies", (encList encodeDeny) x.denies)]

def decodePolicy {N : Type} [tolean.TypeScript.JSNumber N] : Option (Val N) → access.Rbac.Policy
  | some (.obj fs) => { bindings := (decList decodeBinding) (fs.lookup "bindings"), grants := (decList decodeGrant) (fs.lookup "grants"), groups := (decList decodeMembership) (fs.lookup "groups"), denies := (decList decodeDeny) (fs.lookup "denies") }
  | _ => { bindings := (decList decodeBinding) (none : Option (Val N)), grants := (decList decodeGrant) (none : Option (Val N)), groups := (decList decodeMembership) (none : Option (Val N)), denies := (decList decodeDeny) (none : Option (Val N)) }

@[simp] theorem decodePolicy_encodePolicy {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Policy) : decodePolicy (some (encodePolicy (N := N) x)) = x := by
  cases x; simp [decodePolicy, encodePolicy, List.lookup, encList, encNull]

def encodeRequest {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Request) : Val N := Val.obj [("tenant", Val.str x.tenant), ("principal", Val.str x.principal), ("permission", Val.str x.permission)]

def decodeRequest {N : Type} [tolean.TypeScript.JSNumber N] : Option (Val N) → access.Rbac.Request
  | some (.obj fs) => { tenant := decStr (fs.lookup "tenant"), principal := decStr (fs.lookup "principal"), permission := decStr (fs.lookup "permission") }
  | _ => { tenant := decStr (none : Option (Val N)), principal := decStr (none : Option (Val N)), permission := decStr (none : Option (Val N)) }

@[simp] theorem decodeRequest_encodeRequest {N : Type} [tolean.TypeScript.JSNumber N] (x : access.Rbac.Request) : decodeRequest (some (encodeRequest (N := N) x)) = x := by
  cases x; simp [decodeRequest, encodeRequest, List.lookup, encList, encNull]

theorem inGroup_loop1 {N : Type} [tolean.TypeScript.JSNumber N] (m : tolean.TypeScript.Syntax.Module) (fuel : Nat) (items : List access.Rbac.Membership) (ρ : Env N)
    (hI : ρ.lookup "found" = some (Val.bool (decBool (ρ.lookup "found"))) ∧ ρ.lookup "groups" = some ((encList encodeMembership) ((decList decodeMembership) (ρ.lookup "groups"))) ∧ ρ.lookup "group" = some (Val.str (decStr (ρ.lookup "group"))) ∧ ρ.lookup "principal" = some (Val.str (decStr (ρ.lookup "principal"))) ∧ ρ.lookup "Number" = none ∧ ρ.lookup "NaN" = none ∧ ρ.lookup "Infinity" = none) :
    execLoop m fuel ρ "m" (tolean.TypeScript.Syntax.Stmt.block (sp 44 27 48 4) [(tolean.TypeScript.Syntax.Stmt.ifStmt (sp 45 5 47 6) (tolean.TypeScript.Syntax.Expr.binary (sp 45 9 45 55) tolean.TypeScript.Syntax.BinOp.and (tolean.TypeScript.Syntax.Expr.binary (sp 45 9 45 26) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.member (sp 45 9 45 16) (tolean.TypeScript.Syntax.Expr.ident (sp 45 9 45 10) "m") "group") (tolean.TypeScript.Syntax.Expr.ident (sp 45 21 45 26) "group")) (tolean.TypeScript.Syntax.Expr.binary (sp 45 30 45 55) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.member (sp 45 30 45 41) (tolean.TypeScript.Syntax.Expr.ident (sp 45 30 45 31) "m") "principal") (tolean.TypeScript.Syntax.Expr.ident (sp 45 46 45 55) "principal"))) (tolean.TypeScript.Syntax.Stmt.block (sp 45 57 47 6) [(tolean.TypeScript.Syntax.Stmt.exprStmt (sp 46 7 46 20) (tolean.TypeScript.Syntax.Expr.assign (sp 46 7 46 19) tolean.TypeScript.Syntax.AssignOp.assign (tolean.TypeScript.Syntax.Expr.ident (sp 46 7 46 12) "found") (tolean.TypeScript.Syntax.Expr.bool (sp 46 15 46 19) true)))]) none)]) (List.map encodeMembership items) =
      some (.normal (ρ.set "found" (Val.bool (List.foldl (((fun groups group principal => fun found m =>
        let found :=
          if (m.group = group) ∧ (m.principal = principal) then
            let found := true
            found
          else
            found
        found) ((decList decodeMembership) (ρ.lookup "groups")) (decStr (ρ.lookup "group")) (decStr (ρ.lookup "principal")))) (decBool (ρ.lookup "found")) items)))) := by
  refine execLoop_foldl m fuel "m" _ encodeMembership (fun s ρ => (ρ.set "found" (Val.bool s)))
    (fun ρ => (decBool (ρ.lookup "found"))) (fun ρ => (((fun groups group principal => fun found m =>
        let found :=
          if (m.group = group) ∧ (m.principal = principal) then
            let found := true
            found
          else
            found
        found) ((decList decodeMembership) (ρ.lookup "groups")) (decStr (ρ.lookup "group")) (decStr (ρ.lookup "principal"))))) (fun ρ => ρ.lookup "found" = some (Val.bool (decBool (ρ.lookup "found"))) ∧ ρ.lookup "groups" = some ((encList encodeMembership) ((decList decodeMembership) (ρ.lookup "groups"))) ∧ ρ.lookup "group" = some (Val.str (decStr (ρ.lookup "group"))) ∧ ρ.lookup "principal" = some (Val.str (decStr (ρ.lookup "principal"))) ∧ ρ.lookup "Number" = none ∧ ρ.lookup "NaN" = none ∧ ρ.lookup "Infinity" = none) ?_ ?_ ?_ items ρ hI
  · intro ρ s x hI
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hI
    try simp only []
    generalize decBool (ρ.lookup "found") = v0 at h0 ⊢
    generalize (decList decodeMembership) (ρ.lookup "groups") = v1 at h1 ⊢
    generalize decStr (ρ.lookup "group") = v2 at h2 ⊢
    generalize decStr (ρ.lookup "principal") = v3 at h3 ⊢
    certify_tac [Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits, h0, h1, h2, h3, h4, h5, h6]
  · intro s ρ; simp [Env.length_set]
  · intro ρ hI
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hI
    try simp only []
    generalize decBool (ρ.lookup "found") = v0 at h0 ⊢
    simp [Env.set_of_lookup _ _ _ h0]

theorem inGroup_cert {N : Type} [tolean.TypeScript.JSNumber N] (groups : _) (group : _) (principal : _) :
    run (N := N) program "inGroup" [((encList encodeMembership) groups), (Val.str group), (Val.str principal)] = some (Val.bool (access.Rbac.inGroup groups group principal)) := by
  certify_tac [program, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, inGroup_loop1, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits]

theorem isMember_cert {N : Type} [tolean.TypeScript.JSNumber N] (groups : _) (member : _) (principal : _) :
    run (N := N) program "isMember" [((encList encodeMembership) groups), (Val.str member), (Val.str principal)] = some (Val.bool (access.Rbac.isMember groups member principal)) := by
  certify_tac [program, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, inGroup_loop1, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits]

theorem roleGrants_loop1 {N : Type} [tolean.TypeScript.JSNumber N] (m : tolean.TypeScript.Syntax.Module) (fuel : Nat) (items : List access.Rbac.Grant) (ρ : Env N)
    (hI : ρ.lookup "found" = some (Val.bool (decBool (ρ.lookup "found"))) ∧ ρ.lookup "grants" = some ((encList encodeGrant) ((decList decodeGrant) (ρ.lookup "grants"))) ∧ ρ.lookup "role" = some (Val.str (decStr (ρ.lookup "role"))) ∧ ρ.lookup "permission" = some (Val.str (decStr (ρ.lookup "permission"))) ∧ ρ.lookup "Number" = none ∧ ρ.lookup "NaN" = none ∧ ρ.lookup "Infinity" = none) :
    execLoop m fuel ρ "g" (tolean.TypeScript.Syntax.Stmt.block (sp 59 27 63 4) [(tolean.TypeScript.Syntax.Stmt.ifStmt (sp 60 5 62 6) (tolean.TypeScript.Syntax.Expr.binary (sp 60 9 60 55) tolean.TypeScript.Syntax.BinOp.and (tolean.TypeScript.Syntax.Expr.binary (sp 60 9 60 24) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.member (sp 60 9 60 15) (tolean.TypeScript.Syntax.Expr.ident (sp 60 9 60 10) "g") "role") (tolean.TypeScript.Syntax.Expr.ident (sp 60 20 60 24) "role")) (tolean.TypeScript.Syntax.Expr.binary (sp 60 28 60 55) tolean.TypeScript.Syntax.BinOp.strictEq (tolean.TypeScript.Syntax.Expr.member (sp 60 28 60 40) (tolean.TypeScript.Syntax.Expr.ident (sp 60 28 60 29) "g") "permission") (tolean.TypeScript.Syntax.Expr.ident (sp 60 45 60 55) "permission"))) (tolean.TypeScript.Syntax.Stmt.block (sp 60 57 62 6) [(tolean.TypeScript.Syntax.Stmt.exprStmt (sp 61 7 61 20) (tolean.TypeScript.Syntax.Expr.assign (sp 61 7 61 19) tolean.TypeScript.Syntax.AssignOp.assign (tolean.TypeScript.Syntax.Expr.ident (sp 61 7 61 12) "found") (tolean.TypeScript.Syntax.Expr.bool (sp 61 15 61 19) true)))]) none)]) (List.map encodeGrant items) =
      some (.normal (ρ.set "found" (Val.bool (List.foldl (((fun grants role permission => fun found g =>
        let found :=
          if (g.role = role) ∧ (g.permission = permission) then
            let found := true
            found
          else
            found
        found) ((decList decodeGrant) (ρ.lookup "grants")) (decStr (ρ.lookup "role")) (decStr (ρ.lookup "permission")))) (decBool (ρ.lookup "found")) items)))) := by
  refine execLoop_foldl m fuel "g" _ encodeGrant (fun s ρ => (ρ.set "found" (Val.bool s)))
    (fun ρ => (decBool (ρ.lookup "found"))) (fun ρ => (((fun grants role permission => fun found g =>
        let found :=
          if (g.role = role) ∧ (g.permission = permission) then
            let found := true
            found
          else
            found
        found) ((decList decodeGrant) (ρ.lookup "grants")) (decStr (ρ.lookup "role")) (decStr (ρ.lookup "permission"))))) (fun ρ => ρ.lookup "found" = some (Val.bool (decBool (ρ.lookup "found"))) ∧ ρ.lookup "grants" = some ((encList encodeGrant) ((decList decodeGrant) (ρ.lookup "grants"))) ∧ ρ.lookup "role" = some (Val.str (decStr (ρ.lookup "role"))) ∧ ρ.lookup "permission" = some (Val.str (decStr (ρ.lookup "permission"))) ∧ ρ.lookup "Number" = none ∧ ρ.lookup "NaN" = none ∧ ρ.lookup "Infinity" = none) ?_ ?_ ?_ items ρ hI
  · intro ρ s x hI
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hI
    try simp only []
    generalize decBool (ρ.lookup "found") = v0 at h0 ⊢
    generalize (decList decodeGrant) (ρ.lookup "grants") = v1 at h1 ⊢
    generalize decStr (ρ.lookup "role") = v2 at h2 ⊢
    generalize decStr (ρ.lookup "permission") = v3 at h3 ⊢
    certify_tac [Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, inGroup_loop1, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits, h0, h1, h2, h3, h4, h5, h6]
  · intro s ρ; simp [Env.length_set]
  · intro ρ hI
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hI
    try simp only []
    generalize decBool (ρ.lookup "found") = v0 at h0 ⊢
    simp [Env.set_of_lookup _ _ _ h0]

theorem roleGrants_cert {N : Type} [tolean.TypeScript.JSNumber N] (grants : _) (role : _) (permission : _) :
    run (N := N) program "roleGrants" [((encList encodeGrant) grants), (Val.str role), (Val.str permission)] = some (Val.bool (access.Rbac.roleGrants grants role permission)) := by
  certify_tac [program, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, inGroup_loop1, roleGrants_loop1, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits]

theorem bindingAllows_cert {N : Type} [tolean.TypeScript.JSNumber N] (p : _) (b : _) (req : _) :
    run (N := N) program "bindingAllows" [(encodePolicy p), (encodeBinding b), (encodeRequest req)] = some (Val.bool (access.Rbac.bindingAllows p b req)) := by
  certify_tac [program, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, inGroup_loop1, roleGrants_loop1, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits]

theorem denyApplies_cert {N : Type} [tolean.TypeScript.JSNumber N] (p : _) (d : _) (req : _) :
    run (N := N) program "denyApplies" [(encodePolicy p), (encodeDeny d), (encodeRequest req)] = some (Val.bool (access.Rbac.denyApplies p d req)) := by
  certify_tac [program, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, inGroup_loop1, roleGrants_loop1, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits]

theorem allowed_loop1 {N : Type} [tolean.TypeScript.JSNumber N] (m : tolean.TypeScript.Syntax.Module) (hm : m = program) (fuel : Nat) (items : List access.Rbac.Binding) (ρ : Env N)
    (hI : ρ.lookup "found" = some (Val.bool (decBool (ρ.lookup "found"))) ∧ ρ.lookup "p" = some (encodePolicy (decodePolicy (ρ.lookup "p"))) ∧ ρ.lookup "req" = some (encodeRequest (decodeRequest (ρ.lookup "req"))) ∧ ρ.lookup "Number" = none ∧ ρ.lookup "NaN" = none ∧ ρ.lookup "Infinity" = none) :
    execLoop m (fuel + 3) ρ "b" (tolean.TypeScript.Syntax.Stmt.block (sp 79 31 83 4) [(tolean.TypeScript.Syntax.Stmt.ifStmt (sp 80 5 82 6) (tolean.TypeScript.Syntax.Expr.call (sp 80 9 80 33) (tolean.TypeScript.Syntax.Expr.ident (sp 80 9 80 22) "bindingAllows") [(tolean.TypeScript.Syntax.Expr.ident (sp 80 23 80 24) "p"), (tolean.TypeScript.Syntax.Expr.ident (sp 80 26 80 27) "b"), (tolean.TypeScript.Syntax.Expr.ident (sp 80 29 80 32) "req")]) (tolean.TypeScript.Syntax.Stmt.block (sp 80 35 82 6) [(tolean.TypeScript.Syntax.Stmt.exprStmt (sp 81 7 81 20) (tolean.TypeScript.Syntax.Expr.assign (sp 81 7 81 19) tolean.TypeScript.Syntax.AssignOp.assign (tolean.TypeScript.Syntax.Expr.ident (sp 81 7 81 12) "found") (tolean.TypeScript.Syntax.Expr.bool (sp 81 15 81 19) true)))]) none)]) (List.map encodeBinding items) =
      some (.normal (ρ.set "found" (Val.bool (List.foldl (((fun p req => fun found b =>
        let found :=
          if (access.Rbac.bindingAllows p b req) then
            let found := true
            found
          else
            found
        found) (decodePolicy (ρ.lookup "p")) (decodeRequest (ρ.lookup "req")))) (decBool (ρ.lookup "found")) items)))) := by
  refine execLoop_foldl m (fuel + 3) "b" _ encodeBinding (fun s ρ => (ρ.set "found" (Val.bool s)))
    (fun ρ => (decBool (ρ.lookup "found"))) (fun ρ => (((fun p req => fun found b =>
        let found :=
          if (access.Rbac.bindingAllows p b req) then
            let found := true
            found
          else
            found
        found) (decodePolicy (ρ.lookup "p")) (decodeRequest (ρ.lookup "req"))))) (fun ρ => ρ.lookup "found" = some (Val.bool (decBool (ρ.lookup "found"))) ∧ ρ.lookup "p" = some (encodePolicy (decodePolicy (ρ.lookup "p"))) ∧ ρ.lookup "req" = some (encodeRequest (decodeRequest (ρ.lookup "req"))) ∧ ρ.lookup "Number" = none ∧ ρ.lookup "NaN" = none ∧ ρ.lookup "Infinity" = none) ?_ ?_ ?_ items ρ hI
  · intro ρ s x hI
    subst hm
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hI
    try simp only []
    generalize decBool (ρ.lookup "found") = v0 at h0 ⊢
    generalize decodePolicy (ρ.lookup "p") = v1 at h1 ⊢
    generalize decodeRequest (ρ.lookup "req") = v2 at h2 ⊢
    certify_tac [program, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, inGroup_loop1, roleGrants_loop1, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits, h0, h1, h2, h3, h4, h5]
  · intro s ρ; simp [Env.length_set]
  · intro ρ hI
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hI
    try simp only []
    generalize decBool (ρ.lookup "found") = v0 at h0 ⊢
    simp [Env.set_of_lookup _ _ _ h0]

theorem allowed_cert {N : Type} [tolean.TypeScript.JSNumber N] (p : _) (req : _) :
    run (N := N) program "allowed" [(encodePolicy p), (encodeRequest req)] = some (Val.bool (access.Rbac.allowed p req)) := by
  certify_tac [program, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, inGroup_loop1, roleGrants_loop1, allowed_loop1, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits]

theorem denied_loop1 {N : Type} [tolean.TypeScript.JSNumber N] (m : tolean.TypeScript.Syntax.Module) (hm : m = program) (fuel : Nat) (items : List access.Rbac.Deny) (ρ : Env N)
    (hI : ρ.lookup "found" = some (Val.bool (decBool (ρ.lookup "found"))) ∧ ρ.lookup "p" = some (encodePolicy (decodePolicy (ρ.lookup "p"))) ∧ ρ.lookup "req" = some (encodeRequest (decodeRequest (ρ.lookup "req"))) ∧ ρ.lookup "Number" = none ∧ ρ.lookup "NaN" = none ∧ ρ.lookup "Infinity" = none) :
    execLoop m (fuel + 3) ρ "d" (tolean.TypeScript.Syntax.Stmt.block (sp 89 29 93 4) [(tolean.TypeScript.Syntax.Stmt.ifStmt (sp 90 5 92 6) (tolean.TypeScript.Syntax.Expr.call (sp 90 9 90 31) (tolean.TypeScript.Syntax.Expr.ident (sp 90 9 90 20) "denyApplies") [(tolean.TypeScript.Syntax.Expr.ident (sp 90 21 90 22) "p"), (tolean.TypeScript.Syntax.Expr.ident (sp 90 24 90 25) "d"), (tolean.TypeScript.Syntax.Expr.ident (sp 90 27 90 30) "req")]) (tolean.TypeScript.Syntax.Stmt.block (sp 90 33 92 6) [(tolean.TypeScript.Syntax.Stmt.exprStmt (sp 91 7 91 20) (tolean.TypeScript.Syntax.Expr.assign (sp 91 7 91 19) tolean.TypeScript.Syntax.AssignOp.assign (tolean.TypeScript.Syntax.Expr.ident (sp 91 7 91 12) "found") (tolean.TypeScript.Syntax.Expr.bool (sp 91 15 91 19) true)))]) none)]) (List.map encodeDeny items) =
      some (.normal (ρ.set "found" (Val.bool (List.foldl (((fun p req => fun found d =>
        let found :=
          if (access.Rbac.denyApplies p d req) then
            let found := true
            found
          else
            found
        found) (decodePolicy (ρ.lookup "p")) (decodeRequest (ρ.lookup "req")))) (decBool (ρ.lookup "found")) items)))) := by
  refine execLoop_foldl m (fuel + 3) "d" _ encodeDeny (fun s ρ => (ρ.set "found" (Val.bool s)))
    (fun ρ => (decBool (ρ.lookup "found"))) (fun ρ => (((fun p req => fun found d =>
        let found :=
          if (access.Rbac.denyApplies p d req) then
            let found := true
            found
          else
            found
        found) (decodePolicy (ρ.lookup "p")) (decodeRequest (ρ.lookup "req"))))) (fun ρ => ρ.lookup "found" = some (Val.bool (decBool (ρ.lookup "found"))) ∧ ρ.lookup "p" = some (encodePolicy (decodePolicy (ρ.lookup "p"))) ∧ ρ.lookup "req" = some (encodeRequest (decodeRequest (ρ.lookup "req"))) ∧ ρ.lookup "Number" = none ∧ ρ.lookup "NaN" = none ∧ ρ.lookup "Infinity" = none) ?_ ?_ ?_ items ρ hI
  · intro ρ s x hI
    subst hm
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hI
    try simp only []
    generalize decBool (ρ.lookup "found") = v0 at h0 ⊢
    generalize decodePolicy (ρ.lookup "p") = v1 at h1 ⊢
    generalize decodeRequest (ρ.lookup "req") = v2 at h2 ⊢
    certify_tac [program, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, inGroup_loop1, roleGrants_loop1, allowed_loop1, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits, h0, h1, h2, h3, h4, h5]
  · intro s ρ; simp [Env.length_set]
  · intro ρ hI
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hI
    try simp only []
    generalize decBool (ρ.lookup "found") = v0 at h0 ⊢
    simp [Env.set_of_lookup _ _ _ h0]

theorem denied_cert {N : Type} [tolean.TypeScript.JSNumber N] (p : _) (req : _) :
    run (N := N) program "denied" [(encodePolicy p), (encodeRequest req)] = some (Val.bool (access.Rbac.denied p req)) := by
  certify_tac [program, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, inGroup_loop1, roleGrants_loop1, allowed_loop1, denied_loop1, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits]

theorem permits_cert {N : Type} [tolean.TypeScript.JSNumber N] (p : _) (req : _) :
    run (N := N) program "permits" [(encodePolicy p), (encodeRequest req)] = some (Val.bool (access.Rbac.permits p req)) := by
  certify_tac [program, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeBinding, decodeBinding, encodeGrant, decodeGrant, encodeMembership, decodeMembership, encodeDeny, decodeDeny, encodePolicy, decodePolicy, encodeRequest, decodeRequest, inGroup_loop1, roleGrants_loop1, allowed_loop1, denied_loop1, access.Rbac.inGroup, access.Rbac.isMember, access.Rbac.roleGrants, access.Rbac.bindingAllows, access.Rbac.denyApplies, access.Rbac.allowed, access.Rbac.denied, access.Rbac.permits]

end access.RbacCert
