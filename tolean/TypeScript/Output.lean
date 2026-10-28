import tolean.Sexp
import tolean.Source

/-!
The Lean code that the TypeScript translator writes, as a syntax tree.

The translator builds this tree, and `print` writes it as text. Each
constructor is one form that the output can take, and it prints the way the
translator wrote that form when it built strings. A later phase gives the tree
a meaning, so that a theorem can state what the translator writes for every
program it accepts.

The printer is total, and it reads nothing but the tree and the names of the
file (`Names`).
-/
namespace tolean.TypeScript.Output

/-- A Lean type in the output. -/
inductive Ty where
  | int | bool | string
  /-- The number type parameter, `N`. -/
  | number
  /-- `Option Empty`, the type of `null` alone. -/
  | null
  | option (value : Ty)
  | list (elem : Ty)
  /-- A structure of the program: one that the file declares, or one that it
  imports. -/
  | struct (ref : DeclRef)
deriving BEq, Repr, Inhabited

/-- `+`, `-` and `*` on `Int`. -/
inductive IntOp where
  | add | sub | mul
deriving BEq, Repr, Inhabited

/-- An order on `Int`, which is a `Prop`. -/
inductive Order where
  | lt | le | gt | ge
deriving BEq, Repr, Inhabited

/-- `Int.tdiv` and `Int.tmod`. -/
inductive Division where
  | tdiv | tmod
deriving BEq, Repr, Inhabited

/-- An operation of the abstract number model `JSNumber` on two numbers. -/
inductive NumberOp where
  | add | sub | mul | lt | le | eq
deriving BEq, Repr, Inhabited

/-- A constant of the number model. -/
inductive NumberConstant where
  | nan | posInf | negInf
deriving BEq, Repr, Inhabited

/-- A test of the number model on one number. -/
inductive NumberTest where
  | isSafeInteger | isNaN | isFinite
deriving BEq, Repr, Inhabited

/-- A Lean expression in the output. Some are a `Prop`, such as `a < b`; the
translator knows which, and wraps one in `decide` where Lean needs a `Bool`. -/
inductive Expr where
  /-- `(n : Int)`. The translator gives it only a literal's value, which is
  not negative. -/
  | int (n : Int)
  /-- `(JSNumber.ofSafeInt (N := N) (n : Int))`. -/
  | number (n : Int)
  /-- `(JSNumber.nan (N := N))`. -/
  | numberConstant (c : NumberConstant)
  | none
  | bool (b : Bool)
  | string (s : String)
  | var (name : String)
  /-- `x.f`, or `(e).f` when `wrap` is true. -/
  | field (obj : Expr) (wrap : Bool) (name : String)
  /-- `¬(p)`, on a `Prop`. -/
  | propNot (p : Expr)
  /-- `!(b)`, on a `Bool`. -/
  | not (b : Expr)
  /-- `(-a)`, on an `Int`. -/
  | neg (a : Expr)
  /-- `(JSNumber.neg a)`. -/
  | numberNeg (a : Expr)
  /-- `(if c then a else b)`. -/
  | ite (c a b : Expr)
  /-- `(f (N := N) a b)`: a call of a function of the program, one that the
  file declares or one that it imports. -/
  | call (ref : DeclRef) (args : List Expr)
  /-- `([a, b] : List T)`, where `elem` is `T`. -/
  | list (elems : List Expr) (elem : Ty)
  /-- `({ f := a, g := b } : S)`. -/
  | struct (fields : List (String × Expr)) (ref : DeclRef)
  /-- `a.isNone`. -/
  | isNone (a : Expr)
  /-- `a.isSome`. -/
  | isSome (a : Expr)
  /-- `(match x with | none => a | some x => b)`. -/
  | matchNull (name : String) (whenNull whenValue : Expr)
  /-- `(a + b)`. -/
  | intOp (op : IntOp) (a b : Expr)
  /-- `a < b`, a `Prop`. -/
  | order (op : Order) (a b : Expr)
  /-- `(Int.tdiv a b)`. -/
  | division (op : Division) (a b : Expr)
  /-- `(JSNumber.add a b)`. -/
  | numberOp (op : NumberOp) (a b : Expr)
  /-- `!(JSNumber.eq a b)`. -/
  | numberNe (a b : Expr)
  /-- `a = b`, a `Prop`. -/
  | eq (a b : Expr)
  /-- `a ≠ b`, a `Prop`. -/
  | ne (a b : Expr)
  /-- `(p) ∧ (q)`, on two `Prop`s. -/
  | propAnd (p q : Expr)
  /-- `(p) ∨ (q)`, on two `Prop`s. -/
  | propOr (p q : Expr)
  /-- `(a && b)`, on two `Bool`s. -/
  | and (a b : Expr)
  /-- `(a || b)`, on two `Bool`s. -/
  | or (a b : Expr)
  /-- `decide (p)`: a `Prop` as a `Bool`. -/
  | decide (p : Expr)
  /-- `(JSNumber.isNaN a)`, or `(JSNumber.toSafeInt a).isSome`. -/
  | numberTest (test : NumberTest) (a : Expr)
  /-- `xs ++ [a]`: the new value of an owned array after a push. -/
  | push (name : String) (a : Expr)
  /-- `x + a`: the new value of a `let` local after `x += a`. -/
  | update (op : IntOp) (name : String) (a : Expr)
deriving Repr, Inhabited

/-- What a certificate needs to know about a loop, besides its code. The
printer does not read it. -/
structure LoopInfo where
  /-- The span of the `for…of` statement. -/
  span : Span
  /-- The types of the locals that the loop changes, in the order of the state. -/
  stateTypes : List Ty
  /-- The type of the elements. -/
  elem : Ty
  /-- The other locals in scope at the loop, in the order they were declared. -/
  scope : List (String × Ty)
deriving Repr, Inhabited

/-- The body of a function: `let`s that end in a value. -/
inductive Body where
  /-- The value of the function. -/
  | value (e : Expr)
  /-- The locals that a branch or a loop body changes: `x` or `(x, y)`. -/
  | state (names : List String)
  /-- `let x := e`, then `rest`. -/
  | «let» (name : String) (e : Expr) (rest : Body)
  /-- `let xs : T := [a, b]`: an owned array, then `rest`. -/
  | letArray (name : String) (type : Ty) (elems : List Expr) (rest : Body)
  /-- `if c then … else …`. -/
  | ite (c : Expr) (whenTrue whenFalse : Body)
  /-- `match x with | none => … | some x => …`. -/
  | matchNull (name : String) (whenNull whenValue : Body)
  /-- `let (x, y) := branch`, where `branch` is an `ite` or a `matchNull`
  that ends in the state, then `rest`. -/
  | letState (names : List String) (branch : Body) (rest : Body)
  /-- `let (x, y) := List.foldl (fun (x, y) e => body) (x, y) items`, then
  `rest`. -/
  | fold (names : List String) (element : String) (body : Body) (items : Expr) (rest : Body)
      (info : LoopInfo)
deriving Repr, Inhabited

/-- A declaration in the output. -/
inductive Decl where
  /-- `structure S where`, with one field per line. -/
  | struct (name : String) (fields : List (String × Ty))
  /-- `def f (x : T) : R :=`, then the body. -/
  | function (name : String) (params : List (String × Ty)) (ret : Ty) (body : Body)
deriving Repr, Inhabited

/-! ### Printing -/

/-- Another file of the program, as the output of a file that imports from it
writes its declarations. -/
structure ImportedFile where
  /-- The namespace of its translation. -/
  ns : String
  /-- Its declarations are generic over the number type. -/
  generic : Bool
  /-- The name under which its declarations bind the number type. -/
  numberVar : String

/-- The names that the printer needs from the file. -/
structure Names where
  /-- Lean names the output uses that the source also declares. The output
  writes them in full from the root, so a source name never hides them. -/
  clashes : List String := []
  /-- The number type parameter: `N`, or a fresh name when the source uses `N`. -/
  numberVar : String := "N"
  /-- The file uses the number model, so every declaration is generic over `N`. -/
  usesNumber : Bool := false
  /-- The namespace of the translation, with a final dot, before the names of
  its structures and functions. The translation itself writes them inside
  that namespace, so it leaves this empty; a certificate, outside it, sets it. -/
  namespacePrefix : String := ""
  /-- The file of the translation. The output writes a declaration of another
  file with the namespace of that file's translation. -/
  file : String := ""
  /-- The files that the file imports from, by path. -/
  imported : List (String × ImportedFile) := []

/-- How the output writes the declaration `r`, and the name under which it
binds the number type when it is generic over it. -/
def Names.ref (names : Names) (r : DeclRef) : String × Option String :=
  if r.file == names.file then
    (names.namespacePrefix ++ r.name, if names.usesNumber then some names.numberVar else none)
  else match names.imported.lookup r.file with
    | some i => (i.ns ++ "." ++ r.name, if i.generic then some i.numberVar else none)
    | none => (r.name, none)

/-- The Lean names the output uses, with their full names from the root. -/
def leanNames : List (String × String) :=
  [("decide", "Decidable.decide"), ("List", "List"), ("Option", "Option"),
   ("some", "Option.some"), ("none", "Option.none"), ("Int", "Int"), ("Bool", "Bool"),
   ("String", "String"), ("JSNumber", "tolean.TypeScript.JSNumber")]

/-- Write the Lean name `name` (or `name.rest`), from the root when the source
declares the same name. -/
def leanName (names : Names) (name : String) : String :=
  let (head, rest) := match name.splitOn "." with
    | h :: t => (h, String.join (t.map ("." ++ ·)))
    | [] => (name, "")
  if names.clashes.contains head then s!"_root_.{(leanNames.lookup head).getD head}{rest}"
  else name

/-- Lean code as an argument: parenthesized unless it is one atom. A prefix
`!` or `¬` takes the rest of the line in Lean, so code that starts with one is
not an atom even without a space: `f !(a) b` reads as `f !((a) b)`. -/
def argument (code : String) : String :=
  if code.contains ' ' || code.startsWith "!" || code.startsWith "¬" then s!"({code})" else code

def wrapped (constructor argument : String) : String :=
  constructor ++ " " ++
    (if argument.contains ' ' && !argument.startsWith "(" then s!"({argument})" else argument)

def tuple (names : List String) : String :=
  match names with
  | [name] => name
  | _ => "(" ++ ", ".intercalate names ++ ")"

def indentBy (by_ : String) (lines : List String) : List String := lines.map (by_ ++ ·)

def indent (lines : List String) : List String := indentBy "  " lines

def Ty.print (names : Names) : Ty → String
  | .int => leanName names "Int"
  | .number => names.numberVar
  | .bool => leanName names "Bool"
  | .string => leanName names "String"
  | .null => s!"({leanName names "Option"} Empty)"
  | .option t => wrapped (leanName names "Option") (t.print names)
  | .list t => wrapped (leanName names "List") (t.print names)
  | .struct ref =>
    match names.ref ref with
    | (name, some _) => s!"({name} {names.numberVar})"
    | (name, Option.none) => name

def IntOp.symbol : IntOp → String
  | .add => "+" | .sub => "-" | .mul => "*"

def Order.symbol : Order → String
  | .lt => "<" | .le => "≤" | .gt => ">" | .ge => "≥"

def Division.name : Division → String
  | .tdiv => "tdiv" | .tmod => "tmod"

def NumberOp.name : NumberOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .lt => "lt" | .le => "le" | .eq => "eq"

def NumberConstant.name : NumberConstant → String
  | .nan => "nan" | .posInf => "posInf" | .negInf => "negInf"

mutual

def Expr.print (names : Names) : Expr → String
  | .int n => s!"({n} : {leanName names "Int"})"
  | .number n =>
    s!"({leanName names "JSNumber"}.ofSafeInt (N := {names.numberVar}) ({n} : {leanName names "Int"}))"
  | .numberConstant c => s!"({leanName names "JSNumber"}.{c.name} (N := {names.numberVar}))"
  | .none => leanName names "none"
  | .bool b => if b then "true" else "false"
  | .string s => Sexp.quote s
  | .var name => name
  | .field obj wrap name =>
    let o := obj.print names
    s!"{if wrap then s!"({o})" else o}.{name}"
  | .propNot p => s!"¬({p.print names})"
  | .not b => s!"!({b.print names})"
  | .neg a => s!"(-{a.print names})"
  | .numberNeg a => s!"({leanName names "JSNumber"}.neg {argument (a.print names)})"
  | .ite c a b => s!"(if {c.print names} then {a.print names} else {b.print names})"
  | .call ref args =>
    -- The function binds the number type under its own name, `N` or a fresh one.
    let head := match names.ref ref with
      | (name, some binder) => [name, s!"({binder} := {names.numberVar})"]
      | (name, Option.none) => [name]
    "(" ++ " ".intercalate (head ++ (Expr.printList names args).map argument) ++ ")"
  | .list elems elem =>
    s!"([{", ".intercalate (Expr.printList names elems)}] : {(Ty.list elem).print names})"
  | .struct fields ref =>
    "({ " ++ ", ".intercalate (Expr.printFields names fields) ++ " } : " ++
      (Ty.struct ref).print names ++ ")"
  | .isNone a => s!"{argument (a.print names)}.isNone"
  | .isSome a => s!"{argument (a.print names)}.isSome"
  | .matchNull name whenNull whenValue =>
    s!"(match {name} with | {leanName names "none"} => {whenNull.print names} | " ++
      s!"{leanName names "some"} {name} => {whenValue.print names})"
  | .intOp op a b => s!"({a.print names} {op.symbol} {b.print names})"
  | .order op a b => s!"{a.print names} {op.symbol} {b.print names}"
  | .division op a b =>
    s!"({leanName names "Int"}.{op.name} {argument (a.print names)} {argument (b.print names)})"
  | .numberOp op a b =>
    s!"({leanName names "JSNumber"}.{op.name} {argument (a.print names)} {argument (b.print names)})"
  | .numberNe a b =>
    s!"!({leanName names "JSNumber"}.eq {argument (a.print names)} {argument (b.print names)})"
  | .eq a b => s!"{a.print names} = {b.print names}"
  | .ne a b => s!"{a.print names} ≠ {b.print names}"
  | .propAnd p q => s!"({p.print names}) ∧ ({q.print names})"
  | .propOr p q => s!"({p.print names}) ∨ ({q.print names})"
  | .and a b => s!"({a.print names} && {b.print names})"
  | .or a b => s!"({a.print names} || {b.print names})"
  | .decide p => s!"{leanName names "decide"} ({p.print names})"
  | .numberTest test a =>
    let js := leanName names "JSNumber"
    let x := argument (a.print names)
    match test with
    | .isSafeInteger => s!"({js}.toSafeInt {x}).isSome"
    | .isNaN => s!"({js}.isNaN {x})"
    | .isFinite => s!"({js}.isFinite {x})"
  | .push name a => s!"{name} ++ [{a.print names}]"
  | .update op name a => s!"{name} {op.symbol} {a.print names}"

def Expr.printList (names : Names) : List Expr → List String
  | [] => []
  | e :: es => e.print names :: Expr.printList names es

def Expr.printFields (names : Names) : List (String × Expr) → List String
  | [] => []
  | (key, e) :: fs => s!"{key} := {e.print names}" :: Expr.printFields names fs

end

/-- The lines of a body. -/
def Body.lines (names : Names) : Body → List String
  | .value e => [e.print names]
  | .state ns => [tuple ns]
  | .let name e rest => s!"let {name} := {e.print names}" :: rest.lines names
  | .letArray name type elems rest =>
    s!"let {name} : {type.print names} := [{", ".intercalate (Expr.printList names elems)}]" ::
      rest.lines names
  | .ite c whenTrue whenFalse =>
    [s!"if {c.print names} then"] ++ indent (whenTrue.lines names) ++ ["else"] ++
      indent (whenFalse.lines names)
  | .matchNull name whenNull whenValue =>
    [s!"match {name} with", s!"| {leanName names "none"} =>"] ++ indent (whenNull.lines names) ++
      [s!"| {leanName names "some"} {name} =>"] ++ indent (whenValue.lines names)
  | .letState ns branch rest =>
    [s!"let {tuple ns} :="] ++ indent (branch.lines names) ++ rest.lines names
  | .fold ns element body items rest _ =>
    let bodyLines := body.lines names
    let lastLine := bodyLines.getLast?.getD ""
    [s!"let {tuple ns} :=", s!"  {leanName names "List.foldl"}", s!"    (fun {tuple ns} {element} =>"] ++
      indentBy "      " (bodyLines.dropLast ++ [lastLine ++ ")"]) ++
      [s!"    {tuple ns} {items.print names}"] ++ rest.lines names

def Decl.print (names : Names) : Decl → String
  | .struct name fields =>
    let generic := if names.usesNumber then s!" ({names.numberVar} : Type)" else ""
    "\n".intercalate (s!"structure {name}{generic} where" ::
      fields.map fun (field, type) => s!"  {field} : {type.print names}")
  | .function name params ret body =>
    let n := names.numberVar
    let generic :=
      if names.usesNumber then s!" \{{n} : Type} [{leanName names "JSNumber"} {n}]" else ""
    let leanParams := params.map fun (param, type) => s!"({param} : {type.print names})"
    "\n".intercalate
      (s!"def {name}{generic} {" ".intercalate leanParams} : {ret.print names} :=" ::
        indent (body.lines names))

end tolean.TypeScript.Output
