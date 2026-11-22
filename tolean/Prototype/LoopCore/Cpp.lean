import tolean.Prototype.LoopCore.C

namespace tolean.Prototype.LoopCore.Cpp

inductive Head where
  | counted (head : C.Head)
  | byValue (binder vector : String)
  | byConstRef (binder vector : String)

def Head.binder : Head → String
  | .counted h => h.binder
  | .byValue x _ | .byConstRef x _ => x

def Head.items : Head → C.Expr
  | .counted h => h.items
  | .byValue _ xs | .byConstRef _ xs => .var xs

/-- The tiny model has no pointer identity. A const reference therefore reads
the element's value, and cannot be assigned or used to mutate the vector. -/
def Head.accepts (body : C.Stmt) : Head → Bool
  | .counted h => h.safe body
  | .byValue x xs | .byConstRef x xs =>
    !(C.writes body).contains xs && !(C.writes body).contains x && x != xs

def values (h : Head) (env : C.Env) : Option (List C.Val) :=
  C.expr env h.items >>= C.semantics.elements

theorem range_head (x xs : String) (env : C.Env) (vs : List Int)
    (h : env xs = .array vs) :
    values (.byValue x xs) env = some (vs.map C.Val.int) ∧
    values (.byConstRef x xs) env = some (vs.map C.Val.int) := by
  simp [values, Head.items, C.expr, h, C.semantics]

def runLoop (h : Head) (body : C.Stmt) (env : C.Env) :
    Option (Outcome C.Env C.Val) := do
  execLoop (fun inner => C.run inner body)
    (fun x outer => some (C.put h.binder x outer))
    (C.semantics.project (C.writes body)) env (← values h env)

def translateLoop (h : Head) (body : C.Stmt) (rest : C.Body) : C.Body :=
  lowerLoop ((C.writes body).map (fun n => (n, .int))) h.binder .int
    (C.translate (C.writes body) body) h.items rest true (some .int)

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
  have t := lowerLoop_sound C.semantics ((C.writes body).map (fun n => (n, .int)))
    h.binder .int (fun inner => C.run inner body)
    (C.translate (C.writes body) body) rest h.items true (some .int)
    (C.body_sound (C.writes body) body) env vs head
  simp only [List.map_map, Function.comp_def] at t
  rw [List.map_id'] at t
  rw [t]
  congr 1
  funext o
  cases o <;> rfl

end tolean.Prototype.LoopCore.Cpp
