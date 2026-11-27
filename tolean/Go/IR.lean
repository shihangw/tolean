import tolean.IR

/-!
The Go extension of the Tolean IR: the operations that the Go translator adds
to the shared IR in `tolean/IR.lean`.

Go adds no types, because its `int`, `int64`, `bool` and `string` are the
shared `Int`, `Bool` and `String`. It adds three operations: `Go.wrap64`,
which wraps an integer into the 64-bit range as Go's arithmetic does, `++` on
strings, which is Go's `+` on strings, and `pure`, which returns a value from
a function that can panic. Such a function returns `Except String T`, and a
panic is `throw` of its message.

`IR/Eval.lean` gives the IR a meaning, so that a theorem can state what the
translator writes for every function it accepts.
-/
namespace tolean.Go.IR

/-- The types that Go adds to the IR: none yet. -/
inductive TyExt where
deriving BEq, Repr, DecidableEq

/-- The operations that Go adds to the IR, each with the number of arguments
it takes. -/
inductive ExprExt where
  /-- `(Go.wrap64 a)`: `a` wrapped into the 64-bit range. -/
  | wrap64
  /-- `(a ++ b)` on two strings. -/
  | append
  /-- `(pure a)`: the value `a` as the result of a function that can panic. -/
  | pure
deriving BEq, Repr, Inhabited, DecidableEq

abbrev Ty := tolean.IR.Ty TyExt
abbrev Expr := tolean.IR.Expr TyExt ExprExt
abbrev Body := tolean.IR.Body TyExt ExprExt
abbrev Decl := tolean.IR.Decl TyExt ExprExt

@[match_pattern] abbrev Expr.wrap64 (a : Expr) : Expr := .ext .wrap64 [a]
@[match_pattern] abbrev Expr.append (a b : Expr) : Expr := .ext .append [a, b]
@[match_pattern] abbrev Expr.pure (a : Expr) : Expr := .ext .pure [a]

/-! ### Printing -/

/-- The Lean names the output uses, with their full names from the root. -/
def leanNames : List (String × String) := tolean.IR.leanNames ++ [("Go", "tolean.Go")]

/-- Write the Lean name `name` (or `name.rest`), from the root when the
package declares the same name. -/
def leanName (names : tolean.IR.Names) (name : String) : String :=
  tolean.IR.leanNameIn leanNames names name

instance : tolean.IR.PrintTy TyExt where
  print _ t := nomatch t
  namesParam _ t := nomatch t
  binders _ := ""
  -- The Go translator writes no map or set type yet. A Go map has no order,
  -- unlike the shared IR's map, so it will need a model of its own.
  map names := leanName names "Std.HashMap"
  set names := leanName names "Std.HashSet"

/-- An operation on its printed arguments. The translator gives each one the
number of arguments it takes, and the printer writes nothing for others. -/
def ExprExt.print (names : tolean.IR.Names) (op : ExprExt) (args : List String) : String :=
  match op, args with
  | .wrap64, [a] => s!"({tolean.IR.wrapped (leanName names "Go.wrap64") a})"
  | .append, [a, b] => s!"({a} ++ {b})"
  | .pure, [a] => s!"({tolean.IR.wrapped (leanName names "pure") a})"
  | _, _ => ""

instance : tolean.IR.PrintOp ExprExt := ⟨ExprExt.print⟩

end tolean.Go.IR
