import tolean.Go.Syntax.Parser
import tolean.Go.Proof.Package

/-! Expression switches and `if` statements with an init statement on the
proved path: the translation and the interpreter agree, and the forms that the
proved path leaves out are refused. -/

open tolean.Go

private def parseDecls (body : String) : Except String (List Syntax.Decl) := do
  match Syntax.parse ("package sw\nfunc F(x int) int {\n" ++ body ++ "\n}\n") with
  | .ok file => return file.decls
  | .error _ => throw "the switch test did not parse"

private def check (body : String) (input expected : Int) : Bool :=
  match parseDecls body with
  | .error _ => false
  | .ok decls =>
    let translated := Pure.translateFuncs decls ["F"]
    translated.length == 1 &&
      IR.runIn (IR.functions (translated.map (·.1))) ⟨"", "F"⟩ [.int input] == some (.int expected) &&
      Eval.runIn (Eval.program decls) "F" [.int input] == some (.int expected)

private def refused (body : String) : Bool :=
  match parseDecls body with
  | .error _ => false
  | .ok decls => (Pure.translateFuncs decls ["F"]).isEmpty

-- A switch with a tag, several values in a case, and a default anywhere.
private def tagged : String :=
  "switch x { case 1, 2: return 10; default: return 0; case 3: return 30 }"
#guard check tagged 1 10
#guard check tagged 2 10
#guard check tagged 3 30
#guard check tagged 4 0
-- A switch without a tag, which falls out to the code after it.
private def tagless : String :=
  "y := 0; switch { case x < 0: y = -1; case x > 0: y = 1 }; return y"
#guard check tagless (-5) (-1)
#guard check tagless 0 0
#guard check tagless 7 1
-- A switch with an init statement, whose name goes out of scope.
private def withInit : String :=
  "r := 0; switch d := x * 2; d { case 4: r = d; default: r = d + 1 }; return r"
#guard check withInit 2 4
#guard check withInit 3 7
-- A case body declares a local of its own.
#guard check "r := 0; switch x { case 1: t := 5; r = t * 2 }; return r" 1 10
-- `if` with an init statement, with and without a return.
#guard check "if d := x - 3; d > 0 { return d } else { return 0 }" 10 7
#guard check "if d := x - 3; d > 0 { return d } else { return 0 }" 1 0
#guard check "r := 1; if d := x * x; d > 10 { r = d }; return r" 4 16
#guard check "r := 1; if d := x * x; d > 10 { r = d }; return r" 2 1
-- An init statement that assigns an outer local.
#guard check "r := 0; if r = x + 1; r > 5 { r = 100 }; return r" 3 4
#guard check "r := 0; if r = x + 1; r > 5 { r = 100 }; return r" 9 100

-- A tag with only a default would evaluate the tag for nothing.
#guard refused "switch x { default: return 1 }"
-- A switch or an init-if that returns must end the function.
#guard refused "if d := x; d > 0 { return d }; return 0"
-- A tagless case must be a boolean, and the types must match.
#guard refused "switch { case x: return 1 }; return 0"
#guard refused "switch x { case \"a\": return 1 }; return 0"
-- `break` in a switch stays refused.
#guard refused "r := 0; switch x { case 1: r = 1; break }; return r"

#print axioms Proof.translate_sound
