import tolean.TypeScript.IR
import tolean.TypeScript.Spec.Eval

/-!
The meaning of the Tolean IR with the TypeScript extension, as an evaluator
over the values of the interpreter in `Spec/Eval.lean`.

Each constructor of `IR.Expr` and `IR.Body` is one form of Lean code.
The evaluator gives it the value that the printed Lean computes, written as a
JavaScript value: an `Int` is `Val.int`, `none` is `Val.null`, `some v` is the
value of `v`, a list is `Val.list`, and a structure is `Val.obj` with its
fields in the declared order. A `let` adds a binding in front, as Lean's
shadowing does, and `let (x, y) := …` gives `x` and `y` their new values. An
operation that TypeScript adds, such as `JSNumber.add`, gets the values of its
arguments, and `ExprExt.apply` gives its value.

`translate_sound` in `Proof/Module.lean` proves one direction for every
program that the translator accepts: when this evaluator gives a value for a
call, the interpreter gives the same value. So this file is trusted to mean
what the printed Lean means, and to give a value where the printed Lean does.
A certificate checks that for its file (`Proof/Link.lean`), so a certified
file does not trust this evaluator.
-/
namespace tolean.TypeScript.IR

open tolean.TypeScript.Eval (Val Env Outcome)

variable {N : Type} [JSNumber N]

/-- The functions of the output of `file`, by name: their parameters and their
body. -/
def functions (decls : List Decl) : List (String × List String × Body) :=
  decls.filterMap fun
    | .function name params _ body => some (name, params.map (·.1), body)
    | .struct .. | .alias .. | .enum .. | .tagged .. => none

/-- The functions of the output of a program, under the file of each: the
output of each file, with that file's path. -/
def functionsOf (program : List (String × List Decl)) : List (DeclRef × List String × Body) :=
  program.flatMap fun (file, decls) =>
    (functions decls).map fun (name, params, body) => (⟨file, name⟩, params, body)

/-- `=` on the values that the output compares: integers, booleans and
strings. -/
def eqVal : Val N → Val N → Option Bool
  | .int a, .int b => some (decide (a = b))
  | .bool a, .bool b => some (decide (a = b))
  | .str a, .str b => some (decide (a = b))
  | _, _ => none

def NumberOp.apply : NumberOp → N → N → Val N
  | .add, a, b => .num (JSNumber.add a b)
  | .sub, a, b => .num (JSNumber.sub a b)
  | .mul, a, b => .num (JSNumber.mul a b)
  | .lt, a, b => .bool (JSNumber.lt a b)
  | .le, a, b => .bool (JSNumber.le a b)
  | .eq, a, b => .bool (JSNumber.eq a b)

def NumberConstant.value : NumberConstant → N
  | .nan => JSNumber.nan | .posInf => JSNumber.posInf | .negInf => JSNumber.negInf

def NumberTest.apply : NumberTest → N → Bool
  | .isSafeInteger, a => (JSNumber.toSafeInt a).isSome
  | .isNaN, a => JSNumber.isNaN a
  | .isFinite, a => JSNumber.isFinite a

/-- An operation that TypeScript adds, on the values of its arguments. -/
def ExprExt.apply : ExprExt → List (Val N) → Option (Val N)
  | .number n, [] => some (.num (JSNumber.ofSafeInt n))
  | .numberConstant c, [] => some (.num c.value)
  | .numberNeg, [.num a] => some (.num (JSNumber.neg a))
  | .numberOp op, [.num a, .num b] => some (op.apply a b)
  | .numberNe, [.num a, .num b] => some (.bool !(JSNumber.eq a b))
  | .numberTest test, [.num a] => some (.bool (test.apply a))
  -- `a === undefined` and `a !== undefined`, as `IsStrictlyEqual` gives them.
  | .isUndefined, [a] => some (.bool (a matches .undefined))
  | .isDefined, [a] => some (.bool !(a matches .undefined))
  -- `a?.f`, as the spec evaluates it.
  | .optField _ _, [.null] | .optField _ _, [.undefined] => some .undefined
  | .optField f _, [.obj fields] => Eval.getProp fields f
  | _, _ => none

/-- The tag of `v`, a value of a tagged union: the string in its tag field
`field`, or the result of `typeof v` when the union has no tag field. -/
def tagOf : Option String → Val N → Option String
  | some field, .obj fields =>
    match fields.lookup field with
    | some (.str k) => some k
    | _ => none
  | some _, _ => none
  | none, v => some v.typeOf

/-- The bindings that `let (x, y) := …` makes: each of `names`, with its value
in `inner`. A name that is bound already gets the new value in its place,
and a new name goes in front. So every lookup gives what Lean's shadowing
gives, and a loop leaves the environment the same length, which a
certificate's loop lemma needs. -/
def bindState (names : List String) (inner outer : Env N) : Option (Env N) :=
  names.foldlM (fun ρ n => do
    let v ← inner.lookup n
    return if (ρ.lookup n).isSome then Eval.Env.set ρ n v else (n, v) :: ρ) outer

mutual

/-- The value of `e`. `fuel` bounds the depth of nested calls. -/
def Expr.eval (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N) :
    Expr → Option (Val N)
  | .int n => some (.int n)
  | .none => some .null
  | .ascribe e _ => Expr.eval fs fuel ρ e
  | .bool b => some (.bool b)
  | .string s => some (.str s)
  | .var name => ρ.lookup name
  -- A constructor of a literal union is its string, as in JS.
  | .enumCase _ member => some (.str member)
  -- A tag field is its string in the object.
  | .tagValue value => some (.str value)
  -- A member of a tagged union is the value of the member: the object of
  -- its structure, or the primitive value itself.
  | .inject _ _ e => Expr.eval fs fuel ρ e
  -- A field that the object does not have is `undefined`, as in JS.
  | .field obj _ name => do
    match ← Expr.eval fs fuel ρ obj with
    | .obj fields => Eval.getProp fields name
    | _ => none
  | .propNot p | .not p => do
    let .bool b ← Expr.eval fs fuel ρ p | none
    return .bool !b
  | .neg a => do
    let .int i ← Expr.eval fs fuel ρ a | none
    return .int (-i)
  | .ite c a b => do
    let .bool t ← Expr.eval fs fuel ρ c | none
    if t then Expr.eval fs fuel ρ a else Expr.eval fs fuel ρ b
  | .call ref args => do
    let vs ← Expr.evalList fs fuel ρ args
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let (params, body) ← fs.lookup ref
      if params.length != vs.length then none
      match ← Body.exec fs fuel (params.zip vs).reverse body with
      | .ret v => some v
      | .normal _ => none
  | .list elems _ => do return .list (← Expr.evalList fs fuel ρ elems)
  | .struct fields _ => do return .obj (← Expr.evalFields fs fuel ρ fields)
  -- A value of `T | null` is never `undefined`. JS tells `undefined` from
  -- `null` with `===` but not with `==`, so the tests of `null` give no value
  -- for it.
  | .isNone a => do
    match ← Expr.eval fs fuel ρ a with
    | .null => return .bool true
    | .undefined => none
    | _ => return .bool false
  | .isSome a => do
    match ← Expr.eval fs fuel ρ a with
    | .null => return .bool false
    | .undefined => none
    | _ => return .bool true
  | .matchNull name whenNull whenValue => do
    match ← ρ.lookup name with
    | .null => Expr.eval fs fuel ρ whenNull
    | .undefined => none
    | _ => Expr.eval fs fuel ρ whenValue
  -- `none` is `null`, or `undefined` for an optional field, and `some v` is
  -- the value of `v`. So both forms take `a` unless it is `null` or
  -- `undefined`, as `??` does, and only then evaluate `b`.
  | .coalesce a b _ => do
    match ← Expr.eval fs fuel ρ a with
    | .null | .undefined => Expr.eval fs fuel ρ b
    | w => some w
  | .intOp op a b => do
    let .int x ← Expr.eval fs fuel ρ a | none
    let .int y ← Expr.eval fs fuel ρ b | none
    return .int (op.apply x y)
  | .order op a b => do
    let .int x ← Expr.eval fs fuel ρ a | none
    let .int y ← Expr.eval fs fuel ρ b | none
    return .bool (op.apply x y)
  | .division op a b => do
    let .int x ← Expr.eval fs fuel ρ a | none
    let .int y ← Expr.eval fs fuel ρ b | none
    return .int (op.apply x y)
  | .eq a b => do
    return .bool (← eqVal (← Expr.eval fs fuel ρ a) (← Expr.eval fs fuel ρ b))
  | .ne a b => do
    return .bool !(← eqVal (← Expr.eval fs fuel ρ a) (← Expr.eval fs fuel ρ b))
  | .propAnd p q | .and p q => do
    let .bool x ← Expr.eval fs fuel ρ p | none
    let .bool y ← Expr.eval fs fuel ρ q | none
    return .bool (x && y)
  | .propOr p q | .or p q => do
    let .bool x ← Expr.eval fs fuel ρ p | none
    let .bool y ← Expr.eval fs fuel ρ q | none
    return .bool (x || y)
  | .decide p => Expr.eval fs fuel ρ p
  | .push name a => do
    let .list xs ← ρ.lookup name | none
    return .list (xs ++ [← Expr.eval fs fuel ρ a])
  | .update op name a => do
    let .int x ← ρ.lookup name | none
    let .int y ← Expr.eval fs fuel ρ a | none
    return .int (op.apply x y)
  | .ext op args => do op.apply (← Expr.evalList fs fuel ρ args)
termination_by e => (fuel, sizeOf e, 0)

def Expr.evalList (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N) :
    List Expr → Option (List (Val N))
  | [] => some []
  | e :: es => do return (← Expr.eval fs fuel ρ e) :: (← Expr.evalList fs fuel ρ es)
termination_by es => (fuel, sizeOf es, 0)

def Expr.evalFields (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N) :
    List (String × Expr) → Option (List (String × Val N))
  | [] => some []
  | (key, e) :: rest => do
    return (key, ← Expr.eval fs fuel ρ e) :: (← Expr.evalFields fs fuel ρ rest)
termination_by fields => (fuel, sizeOf fields, 0)

/-- Run a body: it returns the function's value, or it ends in the state of a
branch or a loop body, with the bindings it has made. -/
def Body.exec (fs : List (DeclRef × List String × Body)) (fuel : Nat) (ρ : Env N) :
    Body → Option (Outcome N)
  | .value e => do return .ret (← Expr.eval fs fuel ρ e)
  | .state _ => some (.normal ρ)
  | .let name e rest => do Body.exec fs fuel ((name, ← Expr.eval fs fuel ρ e) :: ρ) rest
  | .letArray name _ elems rest => do
    Body.exec fs fuel ((name, .list (← Expr.evalList fs fuel ρ elems)) :: ρ) rest
  | .ite c whenTrue whenFalse => do
    let .bool t ← Expr.eval fs fuel ρ c | none
    if t then Body.exec fs fuel ρ whenTrue else Body.exec fs fuel ρ whenFalse
  | .matchNull name whenNull whenValue => do
    match ← ρ.lookup name with
    | .null => Body.exec fs fuel ρ whenNull
    | .undefined => none
    | _ => Body.exec fs fuel ρ whenValue
  -- The tag is a field of the object, or the type of the value, so the
  -- evaluator reads it, as JS does. The arm of the one member left runs only
  -- for its tag, as the printed `match` on its constructor does.
  | .matchTag name _ field tag other whenTag whenOther => do
    let k ← tagOf field (← ρ.lookup name)
    if k == tag then Body.exec fs fuel ρ whenTag
    else if other.all (· == k) then Body.exec fs fuel ρ whenOther else none
  | .letState names branch rest => do
    match ← Body.exec fs fuel ρ branch with
    | .normal inner => Body.exec fs fuel (← bindState names inner ρ) rest
    | .ret _ => none
  | .fold names element body items rest _ => do
    let .list vs ← Expr.eval fs fuel ρ items | none
    Body.exec fs fuel (← Body.runFold fs fuel names element body ρ vs) rest
termination_by b => (fuel, sizeOf b, 0)

/-- `List.foldl` over `items` with the step `fun (names) element => body`: the
bindings of `names` after each element, on top of `ρ`. -/
def Body.runFold (fs : List (DeclRef × List String × Body)) (fuel : Nat) (names : List String)
    (element : String) (body : Body) (ρ : Env N) : List (Val N) → Option (Env N)
  | [] => some ρ
  | x :: xs => do
    match ← Body.exec fs fuel ((element, x) :: ρ) body with
    | .normal inner => Body.runFold fs fuel names element body (← bindState names inner ρ) xs
    | .ret _ => none
termination_by xs => (fuel, sizeOf body, xs.length + 1)

end

/-- Call the function `key` of the output with `args`. -/
def runIn (fs : List (DeclRef × List String × Body)) (key : DeclRef) (args : List (Val N))
    (fuel : Nat := 64) : Option (Val N) := do
  let (params, body) ← fs.lookup key
  if params.length != args.length then none
  match ← Body.exec fs fuel (params.zip args).reverse body with
  | Outcome.ret v => some v
  | Outcome.normal _ => none

end tolean.TypeScript.IR
