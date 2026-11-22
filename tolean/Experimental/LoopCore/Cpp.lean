import tolean.Experimental.LoopCore.C

namespace tolean.Experimental.LoopCore.Cpp

open tolean.Core.Loop

inductive Head where
  | counted (head : C.Head)
  | byValue (span : Span) (binder vector : String)
  | byConstRef (span : Span) (binder vector : String)

def Head.span : Head → Span
  | .counted h => h.span
  | .byValue span _ _ | .byConstRef span _ _ => span

def Head.binder : Head → String
  | .counted h => h.binder
  | .byValue _ x _ | .byConstRef _ x _ => x

def Head.items : Head → C.Expr
  | .counted h => h.items
  | .byValue _ _ xs | .byConstRef _ _ xs => .var xs

/-- The tiny model has no pointer identity. A const reference therefore reads
the element's value, and cannot mutate the vector. This is not a C++ front end. -/
def Head.accepts (body : C.Stmt) : Head → Bool
  | .counted h => h.safe body
  | .byValue _ x xs | .byConstRef _ x xs =>
    !(C.writes body).contains xs && !(C.writes body).contains x && x != xs

def values (h : Head) (env : C.Env) : Option (List C.Val) :=
  C.expr env h.items >>= C.semantics.elements

theorem range_head (x xs : String) (env : C.Env) (vs : List Int)
    (h : env xs = .array vs) :
    values (.byValue default x xs) env = some (vs.map C.Val.int) ∧
    values (.byConstRef default x xs) env = some (vs.map C.Val.int) := by
  simp [values, Head.items, C.expr, h, C.semantics]

def runLoop (h : Head) (body : C.Stmt) (env : C.Env) :
    Option (Outcome C.Env C.Val) := do
  execLoop (fun inner => C.run inner body)
    (fun x outer => some (C.put h.binder x outer))
    (C.semantics.project (C.writes body)) env (← values h env)

def translateLoop (h : Head) (body : C.Stmt) (rest : C.Body) : C.Body :=
  lowerLoop h.span ((C.writes body).map (fun n => (n, .int))) h.binder .int
    (C.translate (C.writes body) body) h.items rest true (some .int)

def translateChecked (h : Head) (body : C.Stmt) (rest : C.Body) : Except String C.Body :=
  if h.accepts body then .ok (translateLoop h body rest)
  else .error "range loop changes its vector or binder, or the counted head is unsafe"

theorem loop_sound (h : Head) (body : C.Stmt) (rest : C.Body) (env : C.Env)
    (vs : List C.Val) (head : values h env = some vs) :
    evalIR C.semantics env (translateLoop h body rest) =
      (do
        match ← runLoop h body env with
        | .normal inner => evalIR C.semantics inner rest
        | .ret v => return .ret v
        | _ => none) := by
  unfold translateLoop runLoop
  rw [head]
  simp only [bind, Option.bind]
  have t := lowerLoop_sound C.semantics h.span ((C.writes body).map (fun n => (n, .int)))
    h.binder .int (fun inner => C.run inner body)
    (C.translate (C.writes body) body) rest h.items true (some .int)
    (C.body_sound (C.writes body) body) env vs head
  simp only [List.map_map, Function.comp_def] at t
  rw [List.map_id'] at t
  rw [t]
  congr 1
  funext o
  cases o <;> rfl

end tolean.Experimental.LoopCore.Cpp
