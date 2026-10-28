-- Certificate written by tolean for src/my-lib/util.ts. Do not edit.
import tolean.TypeScript.Spec.Lemmas.Eval
import tolean.TypeScript.Syntax.Parser
import tolean.TypeScript.Proof.Link
import «my-lib».Util

namespace src.«my-lib».UtilCert

open tolean.TypeScript tolean.TypeScript.Eval tolean.TypeScript.Syntax

-- The proofs pass the same lemmas everywhere, so some go unused.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The program, as the parser read it. -/
def program : tolean.TypeScript.Syntax.Module :=
  { decls := [
  (tolean.TypeScript.Syntax.Decl.function (sp 2 1 4 2) true "inc" [{ span := (sp 2 21 2 30), name := "x", type := (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 2 24 2 30) "bigint")) }] (some (tolean.TypeScript.Syntax.TypeExpr.keyword (sp 2 33 2 39) "bigint"))
    (tolean.TypeScript.Syntax.Stmt.block (sp 2 40 4 2) [(tolean.TypeScript.Syntax.Stmt.returnStmt (sp 3 3 3 17) (some (tolean.TypeScript.Syntax.Expr.binary (sp 3 10 3 16) tolean.TypeScript.Syntax.BinOp.add (tolean.TypeScript.Syntax.Expr.ident (sp 3 10 3 11) "x") (tolean.TypeScript.Syntax.Expr.bigint (sp 3 14 3 16) "1n"))))]))] }

/-- The source file, one line at a time. -/
def sourceLines : List (List Char) := [
  chars!"// Lean reads `my-lib` only as «my-lib».",
  chars!"export function inc(x: bigint): bigint {",
  chars!"  return x + 1n;",
  chars!"}",
  chars!""]

def sourceChars : List Char := tolean.TypeScript.Syntax.joinLines sourceLines

/-- The parser gives `program` for the source: the kernel runs the parser and
compares the trees. So the theorems below are about the source file, and the
printer that wrote `program` need not be trusted. -/
theorem program_parsed : tolean.TypeScript.Syntax.parseChars sourceChars .es2024 = Except.ok program :=
  tolean.TypeScript.Syntax.parseChars_eq_of_parsesTo (by decide +kernel)

/-- The output tree, as the translator gives it for the program. -/
def decls : List tolean.TypeScript.Output.Decl :=
  [tolean.TypeScript.Output.Decl.function
   "inc"
   [("x", tolean.TypeScript.Output.Ty.int)]
   (tolean.TypeScript.Output.Ty.int)
   (tolean.TypeScript.Output.Body.value
     (tolean.TypeScript.Output.Expr.intOp
       (tolean.TypeScript.Output.IntOp.add)
       (tolean.TypeScript.Output.Expr.var "x")
       (tolean.TypeScript.Output.Expr.int 1)))]

/-- The state that the translator starts from. The source text serves only in
the message of a refusal, so the start leaves it out. -/
def start : tolean.TypeScript.Translate.Ctx :=
  { file := "", target := .es2024, src := #[], lineStarts := #[], fuel := 4 * sourceChars.length + 4 }

/-- The translator gives `decls` for the program: the kernel runs it and
compares the trees. With a `link` theorem for each function, the theorems
below then trust neither the translator nor the printer. -/
theorem program_translated : tolean.TypeScript.Proof.translatesTo program start decls = true := by
  decide +kernel

theorem inc_link {N : Type} [tolean.TypeScript.JSNumber N] (x : _) :
    tolean.TypeScript.Output.runIn (N := N) (tolean.TypeScript.Output.functionsOf [("", decls)]) ⟨"", "inc"⟩ [(Val.int x)] =
      some (Val.int (src.«my-lib».Util.inc x)) := by
  link_tac [decls, Env.set_cons, Env.lookup_cons, Env.lookup_set_same, Env.lookup_set_ne, Env.set_set, Env.length_set, encList, encNull, decInt, decBool, decStr, decNum, src.«my-lib».Util.inc]

theorem inc_cert {N : Type} [tolean.TypeScript.JSNumber N] (x : _) :
    run (N := N) program "inc" [(Val.int x)] = some (Val.int (src.«my-lib».Util.inc x)) :=
  tolean.TypeScript.Proof.decls_sound rfl rfl rfl program_translated "inc" _ 64 _
    (inc_link x)

end src.«my-lib».UtilCert
