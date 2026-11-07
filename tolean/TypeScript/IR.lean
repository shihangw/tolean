import tolean.IR

/-!
The TypeScript extension of the Tolean IR: the types and operations that the
TypeScript translator adds to the shared IR in `tolean/IR.lean`.

TypeScript adds the number type of the abstract number model `JSNumber`, and
`Option Empty` as the type of `null` alone. It adds the operations of the
number model, such as `JSNumber.add`. `Ty`, `Expr`, `Body` and `Decl` here
are the shared types with these added, and definitions such as
`Expr.numberOp` name each added form, so that code and proofs can match on
it as on a constructor.

`IR/Eval.lean` gives the IR a meaning, so that a theorem can state what the
translator writes for every program it accepts.
-/
namespace tolean.TypeScript.IR

export tolean.IR (IntOp Order Division Names ImportedFile leanReserved memberName)

/-- An operation of the abstract number model `JSNumber` on two numbers. -/
inductive NumberOp where
  | add | sub | mul | lt | le | eq
deriving BEq, Repr, Inhabited, DecidableEq

/-- A constant of the number model. -/
inductive NumberConstant where
  | nan | posInf | negInf
deriving BEq, Repr, Inhabited, DecidableEq

/-- A test of the number model on one number. -/
inductive NumberTest where
  | isSafeInteger | isNaN | isFinite
deriving BEq, Repr, Inhabited, DecidableEq

/-- The types that TypeScript adds to the IR. -/
inductive TyExt where
  /-- The number type parameter, `N`. -/
  | number
  /-- `Option Empty`, the type of `null` alone. -/
  | null
deriving BEq, Repr, Inhabited, DecidableEq

/-- The operations that TypeScript adds to the IR, each with the number of
arguments it takes. -/
inductive ExprExt where
  /-- `(JSNumber.ofSafeInt (N := N) (n : Int))`, on no arguments. -/
  | number (n : Int)
  /-- `(JSNumber.nan (N := N))`, on no arguments. -/
  | numberConstant (c : NumberConstant)
  /-- `(JSNumber.neg a)`. -/
  | numberNeg
  /-- `(JSNumber.add a b)`. -/
  | numberOp (op : NumberOp)
  /-- `!(JSNumber.eq a b)`. -/
  | numberNe
  /-- `(JSNumber.isNaN a)`, or `(JSNumber.toSafeInt a).isSome`. -/
  | numberTest (test : NumberTest)
  /-- `a.isNone`, on an optional value: `a === undefined`. -/
  | isUndefined
  /-- `a.isSome`, on an optional value: `a !== undefined`. -/
  | isDefined
  /-- `a.map (·.f)`, or `a.bind (·.f)` when the field `f` is optional:
  `a?.f`, which is `undefined` when `a` is `null` or `undefined`. -/
  | optField (name : String) (bind : Bool)
deriving BEq, Repr, Inhabited, DecidableEq

abbrev Ty := tolean.IR.Ty TyExt
abbrev Expr := tolean.IR.Expr TyExt ExprExt
abbrev Body := tolean.IR.Body TyExt ExprExt
abbrev Decl := tolean.IR.Decl TyExt ExprExt
abbrev LoopInfo := tolean.IR.LoopInfo TyExt

/-- The number type parameter, `N`. -/
@[match_pattern] abbrev Ty.number : Ty := .ext .number
/-- `Option Empty`, the type of `null` alone. -/
@[match_pattern] abbrev Ty.null : Ty := .ext .null

@[match_pattern] abbrev Expr.number (n : Int) : Expr := .ext (.number n) []
@[match_pattern] abbrev Expr.numberConstant (c : NumberConstant) : Expr :=
  .ext (.numberConstant c) []
@[match_pattern] abbrev Expr.numberNeg (a : Expr) : Expr := .ext .numberNeg [a]
@[match_pattern] abbrev Expr.numberOp (op : NumberOp) (a b : Expr) : Expr :=
  .ext (.numberOp op) [a, b]
@[match_pattern] abbrev Expr.numberNe (a b : Expr) : Expr := .ext .numberNe [a, b]
@[match_pattern] abbrev Expr.numberTest (test : NumberTest) (a : Expr) : Expr :=
  .ext (.numberTest test) [a]
@[match_pattern] abbrev Expr.isUndefined (a : Expr) : Expr := .ext .isUndefined [a]
@[match_pattern] abbrev Expr.isDefined (a : Expr) : Expr := .ext .isDefined [a]

/-! ### Printing -/

/-- The Lean names the output uses, with their full names from the root. -/
def leanNames : List (String × String) :=
  tolean.IR.leanNames ++
    [("JSNumber", "tolean.TypeScript.JSNumber"), ("JSString", "tolean.TypeScript.JSString")]

/-- Write the Lean name `name` (or `name.rest`), from the root when the source
declares the same name. -/
def leanName (names : Names) (name : String) : String :=
  tolean.IR.leanNameIn leanNames names name

def NumberOp.name : NumberOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .lt => "lt" | .le => "le" | .eq => "eq"

def NumberConstant.name : NumberConstant → String
  | .nan => "nan" | .posInf => "posInf" | .negInf => "negInf"

instance : tolean.IR.PrintTy TyExt where
  print names
    | .number => names.typeParam
    | .null => s!"({leanName names "Option"} Empty)"
  namesParam _
    | .number => true
    | .null => false
  binders names :=
    let n := names.typeParam
    s!" \{{n} : Type} [{leanName names "JSNumber"} {n}]"
  -- A JS string is a list of UTF-16 code units, not a Lean `String`
  -- (`Spec/String.lean`), and a literal encodes its text.
  string names := leanName names "JSString"
  stringLit names s := s!"{leanName names "JSString.ofString"} {tolean.Sexp.quote s}"

open tolean.IR (argument) in
/-- An operation on its printed arguments. The translator gives each one the
number of arguments it takes, and the printer writes nothing more for others. -/
def ExprExt.print (names : Names) (op : ExprExt) (args : List String) : String :=
  let js := leanName names "JSNumber"
  match op, args with
  | .number n, _ =>
    s!"({js}.ofSafeInt (N := {names.typeParam}) ({n} : {leanName names "Int"}))"
  | .numberConstant c, _ => s!"({js}.{c.name} (N := {names.typeParam}))"
  | .numberNeg, [a] => s!"({js}.neg {argument a})"
  | .numberOp op, [a, b] => s!"({js}.{op.name} {argument a} {argument b})"
  | .numberNe, [a, b] => s!"!({js}.eq {argument a} {argument b})"
  | .numberTest .isSafeInteger, [a] => s!"({js}.toSafeInt {argument a}).isSome"
  | .numberTest .isNaN, [a] => s!"({js}.isNaN {argument a})"
  | .numberTest .isFinite, [a] => s!"({js}.isFinite {argument a})"
  | .isUndefined, [a] => s!"{argument a}.isNone"
  | .isDefined, [a] => s!"{argument a}.isSome"
  | .optField f bind, [a] => s!"({argument a}.{if bind then "bind" else "map"} (·.{f}))"
  | _, _ => ""

instance : tolean.IR.PrintOp ExprExt := ⟨ExprExt.print⟩

end tolean.TypeScript.IR
