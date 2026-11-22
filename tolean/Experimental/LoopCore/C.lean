import tolean.Core.Loop

namespace tolean.Experimental.LoopCore.C

open tolean.Core.Loop

inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  | array (xs : List Int)
deriving Repr, DecidableEq

abbrev Env := String → Val

def put (n : String) (v : Val) (env : Env) : Env :=
  fun k => if k = n then v else env k

inductive Op where
  | at | count
deriving Repr

abbrev Expr := IR.Expr Empty Op
abbrev Body := IR.Body Empty Op

def count (a n : Int) : List Int :=
  (List.range (n - a).toNat).map (fun i => a + Int.ofNat i)

def expr (env : Env) : Expr → Option Val
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | .var n => some (env n)
  | .intOp .add a b => do
    let .int a ← expr env a | none
    let .int b ← expr env b | none
    return .int (a + b)
  | .order .lt a b => do
    let .int a ← expr env a | none
    let .int b ← expr env b | none
    return .bool (a < b)
  | .eq a b => do return .bool ((← expr env a) = (← expr env b))
  | .ext .at [a, i] => do
    let .array xs ← expr env a | none
    let .int i ← expr env i | none
    if i < 0 then none else return .int (← xs[i.toNat]?)
  | .ext .count [a, n] => do
    let .int a ← expr env a | none
    let .int n ← expr env n | none
    return .array (count a n)
  | _ => none

def semantics : Semantics Env Val Empty Op where
  expr := expr
  truth | .bool b => some b | _ => none
  elements | .array xs => some (xs.map Val.int) | _ => none
  put := put
  project := fun ns outer inner => some (fun n => if n ∈ ns then inner n else outer n)

/-- This experimental model embeds expressions in the shared IR. Its
continuation-shaped statements are not a parser or a supported C front end. -/
inductive Stmt where
  | skip
  | assign (name : String) (value : Expr) (rest : Stmt)
  | addAssign (name : String) (value : Expr) (rest : Stmt)
  | ite (test : Expr) (yes no : Stmt)
  | brk | cont
  | ret (value : Expr)

def run (env : Env) : Stmt → Option (Outcome Env Val)
  | .skip => some (.normal env)
  | .assign n e rest => do run (put n (← expr env e) env) rest
  | .addAssign n e rest => do
    run (put n (← expr env (.intOp .add (.var n) e)) env) rest
  | .ite c yes no => do
    if ← semantics.truth (← expr env c) then run env yes else run env no
  | .brk => some (.brk env)
  | .cont => some (.cont env)
  | .ret e => return .ret (← expr env e)

def translate (names : List String) : Stmt → Body
  | .skip | .cont => .yield names true
  | .brk => .done names true
  | .ret e => .exit e names
  | .assign n e rest => .let n e (translate names rest)
  | .addAssign n e rest => .let n (.intOp .add (.var n) e) (translate names rest)
  | .ite c yes no => .ite c (translate names yes) (translate names no)

theorem body_sound (names : List String) (body : Stmt) (env : Env) :
    evalIR semantics env (translate names body) = (run env body).map Outcome.lower := by
  induction body generalizing env with
  | skip | brk | cont => rfl
  | ret e => simp [translate, evalIR, run, semantics]; cases expr env e <;> rfl
  | assign n e rest ih =>
    simp only [translate, evalIR, run]
    cases h : expr env e <;> simp [semantics, h]
    exact ih _
  | addAssign n e rest ih =>
    simp only [translate, evalIR, run]
    cases h : expr env (.intOp .add (.var n) e) <;> simp [semantics, h]
    exact ih _
  | ite c yes no ihy ihn =>
    simp only [translate, evalIR, run]
    cases h : expr env c <;> simp [semantics, h]
    rename_i v
    cases v <;> simp
    rename_i b
    cases b <;> simp
    · exact ihn _
    · exact ihy _

def writes : Stmt → List String
  | .assign n _ rest | .addAssign n _ rest => n :: writes rest
  | .ite _ yes no => writes yes ++ writes no
  | _ => []

structure Head where
  span : Span
  binder : String
  start : Int
  bound : Int

/-- The model captures bounds and keeps only the signed-32-bit counted fragment.
This checked wrapper is evidence about the core's shape, not a C checker. -/
def Head.safe (h : Head) (body : Stmt) : Bool :=
  !(writes body).contains h.binder &&
    decide (-(2^31 : Int) ≤ h.start ∧ h.start ≤ 2^31 - 1 ∧
      -(2^31 : Int) ≤ h.bound ∧ h.bound ≤ 2^31 - 1)

def Head.items (h : Head) : Expr := .ext .count [.int h.start, .int h.bound]

theorem head_sound (h : Head) (env : Env) :
    (expr env h.items >>= semantics.elements) = some ((count h.start h.bound).map Val.int) := rfl

def runLoop (h : Head) (body : Stmt) (env : Env) : Option (Outcome Env Val) :=
  execLoop (fun inner => run inner body)
    (fun x outer => some (put h.binder x outer))
    (semantics.project (writes body)) env ((count h.start h.bound).map Val.int)

def translateLoop (h : Head) (body : Stmt) (rest : Body) : Body :=
  lowerLoop h.span ((writes body).map (fun n => (n, .int))) h.binder .int
    (translate (writes body) body) h.items rest true (some .int)

def translateChecked (h : Head) (body : Stmt) (rest : Body) : Except String Body :=
  if h.safe body then .ok (translateLoop h body rest)
  else .error "counted loop changes its binder or has a bound outside signed 32-bit integers"

theorem loop_sound (h : Head) (body : Stmt) (rest : Body) (env : Env) :
    evalIR semantics env (translateLoop h body rest) =
      (do
        match ← runLoop h body env with
        | .normal inner => evalIR semantics inner rest
        | .ret v => return .ret v
        | _ => none) := by
  unfold translateLoop runLoop
  have t := lowerLoop_sound semantics h.span ((writes body).map (fun n => (n, .int)))
    h.binder .int (fun inner => run inner body)
    (translate (writes body) body) rest h.items true (some .int)
    (body_sound (writes body) body) env _ (head_sound h env)
  simp only [List.map_map, Function.comp_def] at t
  rw [List.map_id'] at t
  rw [t]
  congr 1
  funext o
  cases o <;> rfl

end tolean.Experimental.LoopCore.C
