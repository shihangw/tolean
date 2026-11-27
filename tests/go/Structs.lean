import tolean.Go.Syntax.Parser
import tolean.Go.Proof.Package

/-! Structs on the proved path: field reads and writes and composite
literals translate, and the translation and the interpreter agree. The forms
the subset leaves out make the translator refuse the function. -/

open tolean.Go

private def parseDecls (types body : String) : Except String (List Syntax.Decl) := do
  match Syntax.parse ("package k\n" ++ types ++ "\nfunc F(x int) int {\n" ++ body ++ "\n}\n") with
  | .ok file => return file.decls
  | .error _ => throw "the struct test did not parse"

/-- `F` is translated, and both sides give `expected` for `input`. -/
private def check (types body : String) (input expected : Int) : Bool :=
  match parseDecls types body with
  | .error _ => false
  | .ok decls =>
    let translated := Pure.translateFuncs decls ["F"]
    let same : Option (Except Eval.Val Eval.Val) → Bool
      | some (.ok v) => v == .int expected
      | _ => false
    translated.length == 1 &&
      same (IR.runIn (IR.functions (translated.map (·.1))) ⟨"", "F"⟩ [.int input]) &&
      same (Eval.runIn (Eval.program decls) "F" [.int input])

private def refused (types body : String) : Bool :=
  match parseDecls types body with
  | .error _ => false
  | .ok decls => (Pure.translateFuncs decls ["F"]).isEmpty

private def point := "type P struct {\n  X int\n  Y int\n  On bool\n}"

-- Positional, keyed and empty literals, and field reads.
#guard check point "p := P{x, 2, true}; return p.X + p.Y" 5 7
#guard check point "p := P{X: x, Y: 3, On: false}; if p.On { return 0 }; return p.X * p.Y" 4 12
#guard check point "p := P{}; if p.On { return 1 }; return p.X + p.Y" 9 0
-- Field writes change only the field.
#guard check point "p := P{1, 2, false}; p.X = x; p.On = true; if p.On { return p.X + p.Y }; return 0" 10 12
-- A literal's division panics, as Go's does.
#guard check point "if x == 0 { return -1 }; p := P{10 / x, 0, false}; return p.X" 5 2
-- A struct with a field of another struct type, and `var p P` without a value.
#guard refused "type Q struct { A int }\ntype R struct { Q Q }" "r := R{}; return r.Q.A"
#guard refused point "var p P; return p.X"
-- Keys out of order, some keys missing, and struct equality.
#guard refused point "p := P{Y: 1, X: 2, On: true}; return p.X"
#guard refused point "p := P{X: 1}; return p.X"
#guard refused point "p := P{}; q := P{}; if p == q { return 1 }; return 0"
-- Embedded fields.
#guard refused "type A struct { N int }\ntype B struct {\n  A\n  M int\n}" "b := B{}; return b.M"
