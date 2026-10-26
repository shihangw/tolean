/-
Facts about the interpreter in `tolean.TypeScript.Spec.Eval`, for certificates.

They are proved from the interpreter's definitions, so they need no audit. A
certificate for a function with a loop uses `execLoop_foldl`, and it reads
the values of the loop's variables back out of an environment with the
decoders at the end of this file.
-/
import tolean.TypeScript.Spec.Eval

namespace tolean.TypeScript.Eval

/-! ### Environments -/

theorem Env.set_cons (k n : String) (w v : Val) (rest : Env) :
    Env.set ((k, w) :: rest) n v = if k = n then (k, v) :: rest else (k, w) :: Env.set rest n v := by
  by_cases h : k = n <;> simp [Env.set, h]

theorem Env.lookup_cons (k n : String) (w : Val) (rest : Env) :
    List.lookup n ((k, w) :: rest) = if n = k then some w else List.lookup n rest := by
  by_cases h : n = k
  · subst h; simp [List.lookup]
  · have hb : (n == k) = false := by simpa using h
    simp only [List.lookup, hb, h, if_false]

theorem Env.length_set (ρ : Env) (n : String) (v : Val) : (ρ.set n v).length = ρ.length := by
  induction ρ with
  | nil => rfl
  | cons p rest ih => obtain ⟨k, w⟩ := p; rw [Env.set_cons]; split <;> simp [ih]

theorem Env.set_set (ρ : Env) (n : String) (a b : Val) : (ρ.set n a).set n b = ρ.set n b := by
  induction ρ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, w⟩ := p
    by_cases h : k = n <;> simp [Env.set_cons, h, ih]

theorem Env.set_of_lookup (ρ : Env) (n : String) (v : Val) (h : ρ.lookup n = some v) : ρ.set n v = ρ := by
  induction ρ with
  | nil => simp [List.lookup] at h
  | cons p rest ih =>
    obtain ⟨k, w⟩ := p
    rw [Env.lookup_cons] at h
    by_cases hk : k = n
    · subst hk; simp at h; simp [Env.set_cons, h]
    · have : ¬ n = k := fun e => hk e.symm
      simp [this] at h; simp [Env.set_cons, hk, ih h]

theorem Env.lookup_set_same (ρ : Env) (n : String) (v : Val) (h : (ρ.lookup n).isSome) :
    (ρ.set n v).lookup n = some v := by
  induction ρ with
  | nil => simp [List.lookup] at h
  | cons p rest ih =>
    obtain ⟨k, w⟩ := p
    rw [Env.lookup_cons] at h
    by_cases hk : k = n
    · subst hk; simp [Env.set_cons]
    · have : ¬ n = k := fun e => hk e.symm
      simp only [this, if_false] at h
      simp [Env.set_cons, hk, Env.lookup_cons, this, ih h]

theorem Env.lookup_set_ne (ρ : Env) (n k : String) (v : Val) (h : n ≠ k) :
    (ρ.set n v).lookup k = ρ.lookup k := by
  induction ρ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨j, w⟩ := p
    by_cases hj : j = n
    · subst hj; simp [Env.set_cons, Env.lookup_cons, Ne.symm h]
    · simp [Env.set_cons, hj, Env.lookup_cons, ih]

theorem Env.set_comm (ρ : Env) (a b : String) (x y : Val) (h : a ≠ b) :
    (ρ.set a x).set b y = (ρ.set b y).set a x := by
  induction ρ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, w⟩ := p
    by_cases ha : k = a
    · subst ha; simp [Env.set_cons, h]
    · by_cases hb : k = b
      · subst hb; simp [Env.set_cons, ha]
      · simp [Env.set_cons, ha, hb, ih]

/-! A later `set` of a name moves into the earlier `set` of the same name,
past the `set`s of other names in between. The environment keeps the order
of its names, so the result does not depend on the order of the writes. -/

@[simp] theorem Env.set_merge1 (ρ : Env) (a b1 : String) (x z y1 : Val) (h1 : a ≠ b1) :
    ((ρ.set a x).set b1 y1).set a z = ((ρ.set a z).set b1 y1) := by
  simp only [Env.set_comm _ a _ _ _ h1, Env.set_set]

@[simp] theorem Env.set_merge2 (ρ : Env) (a b1 b2 : String) (x z y1 y2 : Val) (h1 : a ≠ b1) (h2 : a ≠ b2) :
    (((ρ.set a x).set b1 y1).set b2 y2).set a z = (((ρ.set a z).set b1 y1).set b2 y2) := by
  simp only [Env.set_comm _ a _ _ _ h2, Env.set_comm _ a _ _ _ h1, Env.set_set]

@[simp] theorem Env.set_merge3 (ρ : Env) (a b1 b2 b3 : String) (x z y1 y2 y3 : Val) (h1 : a ≠ b1) (h2 : a ≠ b2) (h3 : a ≠ b3) :
    ((((ρ.set a x).set b1 y1).set b2 y2).set b3 y3).set a z = ((((ρ.set a z).set b1 y1).set b2 y2).set b3 y3) := by
  simp only [Env.set_comm _ a _ _ _ h3, Env.set_comm _ a _ _ _ h2, Env.set_comm _ a _ _ _ h1, Env.set_set]

@[simp] theorem Env.set_merge4 (ρ : Env) (a b1 b2 b3 b4 : String) (x z y1 y2 y3 y4 : Val) (h1 : a ≠ b1) (h2 : a ≠ b2) (h3 : a ≠ b3) (h4 : a ≠ b4) :
    (((((ρ.set a x).set b1 y1).set b2 y2).set b3 y3).set b4 y4).set a z = (((((ρ.set a z).set b1 y1).set b2 y2).set b3 y3).set b4 y4) := by
  simp only [Env.set_comm _ a _ _ _ h4, Env.set_comm _ a _ _ _ h3, Env.set_comm _ a _ _ _ h2, Env.set_comm _ a _ _ _ h1, Env.set_set]

@[simp] theorem Env.set_merge5 (ρ : Env) (a b1 b2 b3 b4 b5 : String) (x z y1 y2 y3 y4 y5 : Val) (h1 : a ≠ b1) (h2 : a ≠ b2) (h3 : a ≠ b3) (h4 : a ≠ b4) (h5 : a ≠ b5) :
    ((((((ρ.set a x).set b1 y1).set b2 y2).set b3 y3).set b4 y4).set b5 y5).set a z = ((((((ρ.set a z).set b1 y1).set b2 y2).set b3 y3).set b4 y4).set b5 y5) := by
  simp only [Env.set_comm _ a _ _ _ h5, Env.set_comm _ a _ _ _ h4, Env.set_comm _ a _ _ _ h3, Env.set_comm _ a _ _ _ h2, Env.set_comm _ a _ _ _ h1, Env.set_set]

@[simp] theorem Env.set_merge6 (ρ : Env) (a b1 b2 b3 b4 b5 b6 : String) (x z y1 y2 y3 y4 y5 y6 : Val) (h1 : a ≠ b1) (h2 : a ≠ b2) (h3 : a ≠ b3) (h4 : a ≠ b4) (h5 : a ≠ b5) (h6 : a ≠ b6) :
    (((((((ρ.set a x).set b1 y1).set b2 y2).set b3 y3).set b4 y4).set b5 y5).set b6 y6).set a z = (((((((ρ.set a z).set b1 y1).set b2 y2).set b3 y3).set b4 y4).set b5 y5).set b6 y6) := by
  simp only [Env.set_comm _ a _ _ _ h6, Env.set_comm _ a _ _ _ h5, Env.set_comm _ a _ _ _ h4, Env.set_comm _ a _ _ _ h3, Env.set_comm _ a _ _ _ h2, Env.set_comm _ a _ _ _ h1, Env.set_set]

@[simp] theorem Env.set_merge7 (ρ : Env) (a b1 b2 b3 b4 b5 b6 b7 : String) (x z y1 y2 y3 y4 y5 y6 y7 : Val) (h1 : a ≠ b1) (h2 : a ≠ b2) (h3 : a ≠ b3) (h4 : a ≠ b4) (h5 : a ≠ b5) (h6 : a ≠ b6) (h7 : a ≠ b7) :
    ((((((((ρ.set a x).set b1 y1).set b2 y2).set b3 y3).set b4 y4).set b5 y5).set b6 y6).set b7 y7).set a z = ((((((((ρ.set a z).set b1 y1).set b2 y2).set b3 y3).set b4 y4).set b5 y5).set b6 y6).set b7 y7) := by
  simp only [Env.set_comm _ a _ _ _ h7, Env.set_comm _ a _ _ _ h6, Env.set_comm _ a _ _ _ h5, Env.set_comm _ a _ _ _ h4, Env.set_comm _ a _ _ _ h3, Env.set_comm _ a _ _ _ h2, Env.set_comm _ a _ _ _ h1, Env.set_set]

@[simp] theorem Env.set_merge8 (ρ : Env) (a b1 b2 b3 b4 b5 b6 b7 b8 : String) (x z y1 y2 y3 y4 y5 y6 y7 y8 : Val) (h1 : a ≠ b1) (h2 : a ≠ b2) (h3 : a ≠ b3) (h4 : a ≠ b4) (h5 : a ≠ b5) (h6 : a ≠ b6) (h7 : a ≠ b7) (h8 : a ≠ b8) :
    (((((((((ρ.set a x).set b1 y1).set b2 y2).set b3 y3).set b4 y4).set b5 y5).set b6 y6).set b7 y7).set b8 y8).set a z = (((((((((ρ.set a z).set b1 y1).set b2 y2).set b3 y3).set b4 y4).set b5 y5).set b6 y6).set b7 y7).set b8 y8) := by
  simp only [Env.set_comm _ a _ _ _ h8, Env.set_comm _ a _ _ _ h7, Env.set_comm _ a _ _ _ h6, Env.set_comm _ a _ _ _ h5, Env.set_comm _ a _ _ _ h4, Env.set_comm _ a _ _ _ h3, Env.set_comm _ a _ _ _ h2, Env.set_comm _ a _ _ _ h1, Env.set_set]

/-- A loop and a fold agree when one run of the body and one fold step agree. -/
theorem execLoop_foldl {α σ : Type} (m : Syntax.Module) (fuel : Nat) (name : String) (body : Syntax.Stmt)
    (encX : α → Val) (upd : σ → Env → Env) (dec : Env → σ) (step : Env → σ → α → σ) (I : Env → Prop)
    (hbody : ∀ ρ s x, I ρ → execStmt m fuel ((name, encX x) :: upd s ρ) body =
      some (.normal ((name, encX x) :: upd (step ρ s x) ρ)))
    (hlen : ∀ s ρ, (upd s ρ).length = ρ.length)
    (hdec : ∀ ρ, I ρ → upd (dec ρ) ρ = ρ) (xs : List α) (ρ : Env) (hI : I ρ) :
    execLoop m fuel ρ name body (xs.map encX) = some (.normal (upd (xs.foldl (step ρ) (dec ρ)) ρ)) := by
  have key : ∀ (xs : List α) (s : σ), execLoop m fuel (upd s ρ) name body (xs.map encX) =
      some (.normal (upd (xs.foldl (step ρ) s) ρ)) := by
    intro xs
    induction xs with
    | nil => intro s; simp [execLoop]
    | cons x xs ih =>
      intro s
      rw [List.map_cons, execLoop, hbody ρ s x hI]
      simp only [Option.bind_eq_bind, Option.bind_some, List.length_cons, hlen]
      rw [show ρ.length + 1 - ρ.length = 1 by omega, List.drop_one, List.tail_cons, ih, List.foldl_cons]
  rw [← hdec ρ hI] ; exact (by simpa [hdec ρ hI] using key xs (dec ρ))


/-! ### Encoders

A certificate writes each Lean value as a `Val` with these, so that a lemma
can name the encoding of a list or a nullable value. -/

/-- A list as a JS array. -/
def encList {α : Type} (enc : α → Val) (xs : List α) : Val := .list (xs.map enc)

/-- A `T | null` value: `none` is `null`. -/
def encNull {α : Type} (enc : α → Val) : Option α → Val
  | some v => enc v
  | none => .null

@[simp] theorem encNull_some {α : Type} (enc : α → Val) (v : α) : encNull enc (some v) = enc v := rfl
@[simp] theorem encNull_none {α : Type} (enc : α → Val) : encNull enc none = .null := rfl

/-! ### Decoders

A decoder reads a Lean value back out of a variable's value. It gives a
default for a value of the wrong shape, and `dec (some (enc v)) = v` for the
encoder that a certificate uses. -/

def decInt : Option Val → Int
  | some (.int i) => i
  | _ => 0

def decBool : Option Val → Bool
  | some (.bool b) => b
  | _ => false

def decStr : Option Val → String
  | some (.str s) => s
  | _ => ""

def decList {α : Type} (dec : Option Val → α) : Option Val → List α
  | some (.list vs) => vs.map (fun v => dec (some v))
  | _ => []

/-- A `T | null` value: `null` is `none`, and anything else is decoded. -/
def decNull {α : Type} (dec : Option Val → α) : Option Val → Option α
  | some .null => none
  | o => some (dec o)

@[simp] theorem decInt_int (i : Int) : decInt (some (.int i)) = i := rfl
@[simp] theorem decBool_bool (b : Bool) : decBool (some (.bool b)) = b := rfl
@[simp] theorem decStr_str (s : String) : decStr (some (.str s)) = s := rfl

@[simp] theorem decList_list {α : Type} (dec : Option Val → α) (enc : α → Val)
    (h : ∀ x, dec (some (enc x)) = x) (xs : List α) :
    decList dec (some (.list (xs.map enc))) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [decList]

@[simp] theorem decNull_some {α : Type} (dec : Option Val → α) (v : Val) (h : v ≠ .null) :
    decNull dec (some v) = some (dec (some v)) := by
  cases v <;> simp_all [decNull]

/-- `decList` on an array that the program wrote out, such as `[0n]`. -/
@[simp] theorem decList_nil {α : Type} (dec : Option Val → α) : decList dec (some (.list [])) = [] := rfl

@[simp] theorem decList_cons {α : Type} (dec : Option Val → α) (v : Val) (vs : List Val) :
    decList dec (some (.list (v :: vs))) = dec (some v) :: decList dec (some (.list vs)) := rfl

@[simp] theorem decList_encList {α : Type} (dec : Option Val → α) (enc : α → Val)
    (h : ∀ x, dec (some (enc x)) = x) (xs : List α) :
    decList dec (some (encList enc xs)) = xs :=
  decList_list dec enc h xs

@[simp] theorem decNull_encNull {α : Type} (dec : Option Val → α) (enc : α → Val)
    (h : ∀ x, dec (some (enc x)) = x) (hn : ∀ x, enc x ≠ .null) (o : Option α) :
    decNull dec (some (encNull enc o)) = o := by
  cases o with
  | none => rfl
  | some v => simp [decNull_some dec (enc v) (hn v), h]

@[simp] theorem decNull_null {α : Type} (dec : Option Val → α) : decNull dec (some .null) = none := rfl

end tolean.TypeScript.Eval
