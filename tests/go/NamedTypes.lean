import tolean.Go.Syntax.Parser
import tolean.Go.Proof.Package

/-! Types that the package declares over a predeclared type, and conversions
to them, on the proved path: the translation and the interpreter agree, and
the forms that the proved path leaves out make it refuse the function. -/

open tolean.Go

private def parseDecls (src : String) : Except String (List Syntax.Decl) := do
  match Syntax.parse ("package named\n" ++ src) with
  | .ok file => return file.decls
  | .error _ => throw "the named-type test did not parse"

/-- `F` is translated, and both sides give `expected` for `args`. -/
private def check (src : String) (args : List Eval.Val) (expected : Eval.Val) : Bool :=
  match parseDecls src with
  | .error _ => false
  | .ok decls =>
    let translated := Pure.translateFuncs decls ["F"]
    let same : Option (Except Eval.Val Eval.Val) → Bool
      | some (.ok v) => v == expected
      | _ => false
    translated.length == 1 &&
      same (IR.runIn (IR.functions (translated.map (·.1))) ⟨"", "F"⟩ args) &&
      same (Eval.runIn (Eval.program decls) "F" args)

private def refused (src : String) : Bool :=
  match parseDecls src with
  | .error _ => false
  | .ok decls => (Pure.translateFuncs decls ["F"]).isEmpty

private def celsius := "type Celsius int\n"

-- Parameters, results and arithmetic of a named type.
#guard check (celsius ++ "func F(c Celsius) Celsius { return c * 9 / 5 + 32 }") [.int 100] (.int 212)
-- Conversions to and from the named type keep the value.
#guard check (celsius ++ "func F(x int) int { c := Celsius(x); return int(c + 1) }") [.int 4] (.int 5)
#guard check (celsius ++ "func F(x int) int64 { return int64(Celsius(x)) }") [.int (-3)] (.int (-3))
-- The zero value of a named type is that of its underlying type.
#guard check (celsius ++ "func F(x int) Celsius { var c Celsius; return c }") [.int 1] (.int 0)
#guard check ("type Flag bool\nfunc F(x int) bool { var f Flag; if f { return false }; return true }") [.int 0] (.bool true)
#guard check ("type Name string\nfunc F(n Name) bool { var z Name; return n == z }") [.str ""] (.bool true)
#guard check ("type Flag bool\nfunc F(x int) Flag { return Flag(x > 0) }") [.int 1] (.bool true)
-- A typed constant of a named type.
#guard check (celsius ++ "const Boil Celsius = 100\nfunc F(c Celsius) bool { return c >= Boil }") [.int 100]
  (.bool true)
-- An alias names the same type.
#guard check ("type Count = int64\nfunc F(x int) Count { return Count(x) * 2 }") [.int 4] (.int 8)
-- A conversion to a string type, which can turn an integer into a code point.
#guard refused ("type Name string\nfunc F(s string) Name { return Name(s) }")
-- A type over another type of the package, or over a composite type.
#guard refused (celsius ++ "type Temp Celsius\nfunc F(t Temp) Temp { return t }")
#guard refused ("type Pair [2]int\nfunc F(x int) int { var p Pair; return x }")
-- A conversion takes one argument.
#guard refused (celsius ++ "func F(x int) Celsius { return Celsius(x, x) }")
