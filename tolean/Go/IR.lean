import tolean.IR

/-!
The Go extension of the Tolean IR: the operations that the Go translator adds
to the shared IR in `tolean/IR.lean`.

Go adds no types, because its `int`, `int64`, `bool` and `string` are the
shared `Int`, `Bool` and `String`. A `byte` is an `Int` too. It adds
`Go.wrap64`, which wraps an integer into the 64-bit range as Go's arithmetic
does, `++` on strings, which is Go's `+` on strings, `pure`, which returns
a value from a function that can panic, and the tuple of a call's arguments. Such a function returns
`Except String T`, and a panic is `throw` of its message. The operations on
the bytes of a string, `len`, indexing and the orders, are functions of
`tolean/Go/Spec/Basic.lean`.

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
  /-- `(Go.byteLen s)`: `len(s)`, the number of bytes of a string. -/
  | byteLen
  /-- `(Go.byteAt s i)`: `s[i]`, the byte at index `i` of a string. -/
  | byteAt
  /-- `(Go.strLt a b)` and the other orders of strings, as `Bool`s. -/
  | strLt | strLe | strGt | strGe
  /-- `(Go.indexFault s i)`: the message of the panic of `s[i]`, or `""`. -/
  | indexFault
  /-- `(Go.after c m)`: the value `m`, after the output has evaluated `c`. -/
  | after
  /-- `(a, b, …)`: the arguments of a call, evaluated for a test of their
  divisors without the call itself. The output binds it to `_`. -/
  | args
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

/-- Whether the parenthesis that opens `cs` closes only at its end. It skips
string literals, whose parentheses do not count. -/
def oneGroup (cs : List Char) : Bool :=
  go cs 0 false false
where
  /-- `depth` open parentheses, inside a string literal or not, after an
  escaping backslash or not. -/
  go : List Char → Nat → Bool → Bool → Bool
    | [], _, _, _ => false
    | c :: rest, depth, inStr, esc =>
      if inStr then
        if esc then go rest depth true false
        else if c == '\\' then go rest depth true true
        else go rest depth (c != '"') false
      else if c == '"' then go rest depth true false
      else if c == '(' then go rest (depth + 1) false false
      else if c == ')' then
        if depth == 1 then rest.isEmpty else go rest (depth - 1) false false
      else if depth == 0 then false
      else go rest depth false false

/-- A printed argument, in parentheses unless it is a name, a number, or one
group in parentheses. -/
def arg (a : String) : String :=
  -- String.all specializes a slice iterator that calls a private standard-library
  -- helper absent from the WASM build. Traverse the characters instead.
  let atom := a.toList.all fun c => c.isAlphanum || c == '_' || c == '.' || c == '\''
  if (atom && !a.isEmpty) || oneGroup a.toList then a else s!"({a})"

/-- An operation on its printed arguments. The translator gives each one the
number of arguments it takes, and the printer writes nothing for others. -/
def ExprExt.print (names : tolean.IR.Names) (op : ExprExt) (args : List String) : String :=
  match op, args with
  | .wrap64, [a] => s!"({tolean.IR.wrapped (leanName names "Go.wrap64") a})"
  | .append, [a, b] => s!"({a} ++ {b})"
  | .pure, [a] => s!"({tolean.IR.wrapped (leanName names "pure") a})"
  | .byteLen, [a] => s!"({tolean.IR.wrapped (leanName names "Go.byteLen") a})"
  | .byteAt, [a, b] => s!"({leanName names "Go.byteAt"} {arg a} {arg b})"
  | .strLt, [a, b] => s!"({leanName names "Go.strLt"} {arg a} {arg b})"
  | .strLe, [a, b] => s!"({leanName names "Go.strLe"} {arg a} {arg b})"
  | .strGt, [a, b] => s!"({leanName names "Go.strGt"} {arg a} {arg b})"
  | .strGe, [a, b] => s!"({leanName names "Go.strGe"} {arg a} {arg b})"
  | .indexFault, [a, b] => s!"({leanName names "Go.indexFault"} {arg a} {arg b})"
  | .after, [a, b] => s!"({leanName names "Go.after"} {arg a} {arg b})"
  | .args, [a] => a
  | .args, args@(_ :: _) => "(" ++ ", ".intercalate args ++ ")"
  | _, _ => ""

instance : tolean.IR.PrintOp ExprExt := ⟨ExprExt.print⟩

end tolean.Go.IR
