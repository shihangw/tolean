-- Certificate written by tolean for sensor/raise.ts. Do not edit.
import tolean.TypeScript.Spec.Lemmas.Eval
import tolean.TypeScript.Syntax.Parser
import sensor.Raise

namespace sensor.RaiseCert

open tolean.TypeScript tolean.TypeScript.Eval tolean.TypeScript.Syntax

-- The proofs pass the same lemmas everywhere, so some go unused.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The program, as the parser read it. -/
def program : tolean.TypeScript.Syntax.Module :=
  { decls := [
  (tolean.TypeScript.Syntax.Decl.interface (sp 1 1 4 2) true "Gauge" [{ span := (sp 2 3 2 26), readonly := true, name := "level", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 2 19 2 25) "bigint") }, { span := (sp 3 3 3 24), readonly := true, name := "max", optional := false, type := (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 3 17 3 23) "bigint") }]),
  (tolean.TypeScript.Syntax.Decl.function (sp 6 1 11 2) true "raise" [{ span := (sp 6 23 6 31), name := "g", type := (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 6 26 6 31) "Gauge" [])) }, { span := (sp 6 33 6 45), name := "step", type := (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 6 39 6 45) "bigint")) }] (some (tolean.TypeScript.Syntax.TypeExpr.ref (sp 6 48 6 53) "Gauge" []))
    (tolean.TypeScript.Syntax.Stmt.block (sp 6 54 11 2) [(tolean.TypeScript.Syntax.Stmt.ifStmt (sp 7 3 9 4) (tolean.TypeScript.Syntax.Expr.binary (sp 7 7 7 29) tolean.TypeScript.Syntax.BinOp.gt (tolean.TypeScript.Syntax.Expr.binary (sp 7 7 7 21) tolean.TypeScript.Syntax.BinOp.add (tolean.TypeScript.Syntax.Expr.member (sp 7 7 7 14) (tolean.TypeScript.Syntax.Expr.ident (sp 7 7 7 8) "g") "level") (tolean.TypeScript.Syntax.Expr.ident (sp 7 17 7 21) "step")) (tolean.TypeScript.Syntax.Expr.member (sp 7 24 7 29) (tolean.TypeScript.Syntax.Expr.ident (sp 7 24 7 25) "g") "max")) (tolean.TypeScript.Syntax.Stmt.block (sp 7 31 9 4) [(tolean.TypeScript.Syntax.Stmt.returnStmt (sp 8 5 8 41) (some (tolean.TypeScript.Syntax.Expr.object (sp 8 12 8 40) [(tolean.TypeScript.Syntax.Property.keyValue (sp 8 14 8 26) (tolean.TypeScript.Syntax.PropKey.ident "level") (tolean.TypeScript.Syntax.Expr.member (sp 8 21 8 26) (tolean.TypeScript.Syntax.Expr.ident (sp 8 21 8 22) "g") "max")), (tolean.TypeScript.Syntax.Property.keyValue (sp 8 28 8 38) (tolean.TypeScript.Syntax.PropKey.ident "max") (tolean.TypeScript.Syntax.Expr.member (sp 8 33 8 38) (tolean.TypeScript.Syntax.Expr.ident (sp 8 33 8 34) "g") "max"))])))]) none), (tolean.TypeScript.Syntax.Stmt.returnStmt (sp 10 3 10 48) (some (tolean.TypeScript.Syntax.Expr.object (sp 10 10 10 47) [(tolean.TypeScript.Syntax.Property.keyValue (sp 10 12 10 33) (tolean.TypeScript.Syntax.PropKey.ident "level") (tolean.TypeScript.Syntax.Expr.binary (sp 10 19 10 33) tolean.TypeScript.Syntax.BinOp.add (tolean.TypeScript.Syntax.Expr.member (sp 10 19 10 26) (tolean.TypeScript.Syntax.Expr.ident (sp 10 19 10 20) "g") "level") (tolean.TypeScript.Syntax.Expr.ident (sp 10 29 10 33) "step"))), (tolean.TypeScript.Syntax.Property.keyValue (sp 10 35 10 45) (tolean.TypeScript.Syntax.PropKey.ident "max") (tolean.TypeScript.Syntax.Expr.member (sp 10 40 10 45) (tolean.TypeScript.Syntax.Expr.ident (sp 10 40 10 41) "g") "max"))])))]))] }

/-- The source file, one line at a time. -/
def sourceLines : List (List Char) := [
  chars!"export interface Gauge {",
  chars!"  readonly level: bigint;",
  chars!"  readonly max: bigint;",
  chars!"}",
  chars!"",
  chars!"export function raise(g: Gauge, step: bigint): Gauge {",
  chars!"  if (g.level + step > g.max) {",
  chars!"    return { level: g.max, max: g.max };",
  chars!"  }",
  chars!"  return { level: g.level + step, max: g.max };",
  chars!"}",
  chars!""]

def sourceChars : List Char := tolean.TypeScript.Syntax.joinLines sourceLines

/-- The parser gives `program` for the source: the kernel runs the parser and
compares the trees. So the theorems below are about the source file, and the
printer that wrote `program` need not be trusted. -/
theorem program_parsed : tolean.TypeScript.Syntax.parseChars sourceChars .es2024 = Except.ok program :=
  tolean.TypeScript.Syntax.parseChars_eq_of_parsesTo (by decide +kernel)

def encodeGauge {N : Type} [tolean.TypeScript.JSNumber N] (x : sensor.Raise.Gauge) : Val N := Val.obj [("level", Val.int x.level), ("max", Val.int x.max)]

def decodeGauge {N : Type} [tolean.TypeScript.JSNumber N] : Option (Val N) → sensor.Raise.Gauge
  | some (.obj fs) => { level := decInt (fs.lookup "level"), max := decInt (fs.lookup "max") }
  | _ => { level := decInt (none : Option (Val N)), max := decInt (none : Option (Val N)) }

@[simp] theorem decodeGauge_encodeGauge {N : Type} [tolean.TypeScript.JSNumber N] (x : sensor.Raise.Gauge) : decodeGauge (some (encodeGauge (N := N) x)) = x := by
  cases x; simp [decodeGauge, encodeGauge, List.lookup, encList, encNull]

theorem raise_cert {N : Type} [tolean.TypeScript.JSNumber N] (g : _) (step : _) :
    run (N := N) program "raise" [(encodeGauge g), (Val.int step)] = some (encodeGauge (sensor.Raise.raise g step)) := by
  certify_tac [program, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, encodeGauge, decodeGauge, sensor.Raise.raise]

end sensor.RaiseCert
