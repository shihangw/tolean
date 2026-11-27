import tolean.TypeScript.Proof.ExprBase

/-!
The second half of the proof that the translation of an expression means what
the expression means: maps, iteration, array spread and `expr_sound` itself.
`ExprBase` holds the first half, so that each file builds in less time.
-/
namespace tolean.TypeScript.Proof

open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate
open tolean.TypeScript.Eval (Val Outcome)

variable {N : Type} [JSNumber N]

variable (m : Eval.Scope) (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)

/-! ### Maps -/

/-- An owned map, read as its local, means what the name means. -/
theorem ownedMap_sim {env : Translate.Env} {e : Expr} {c : Code} (h : ownedMap? env e = some c) :
    Sim (N := N) m fs fuel env e c.code := by
  intro ρs ρo v ha _ hv
  cases e with
  | ident sp name =>
    simp only [ownedMap?] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [IR.Expr.eval] at hv
      rw [← ha name] at hv
      simp only [Eval.eval, hv]
    · simp at h
  | _ => simp [ownedMap?] at h

/-- The receiver of `size`, `get` or `has` means what the expression means. -/
theorem translateRecv_sim {env : Translate.Env} {e : Expr} {tr : Expr → TM Code} {ctx ctx' : Ctx}
    {c : Code} (htr : ∀ ctx c ctx', tr e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    (h : translateRecv tr env e ctx = .ok c ctx') : Sim (N := N) m fs fuel env e c.code := by
  cases hc : ownedMap? env e with
  | some c' =>
    simp only [translateRecv, hc, pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    exact ownedMap_sim m fs fuel hc
  | none =>
    simp only [translateRecv, hc] at h
    exact htr _ _ _ h

/-- The value of `m.get(k)` or `m.has(k)`, from the entries of the map and the
key. -/
def mapMethodVal (name : String) : Val N → Val N → Option (Val N)
  | .map entries, k =>
    (Eval.mapFind entries k).bind fun found =>
      if name = "get" then some (found.getD .undefined)
      else if name = "has" then some (.bool found.isSome) else none
  | .set elems, x => (Eval.setHas elems x).bind fun found => if name = "has" then some (.bool found) else none
  | _, _ => none

theorem eval_mapMethod (sp sp' : Span) (recv key : Expr) (name : String) (hr : recv.namesGlobal = false)
    (hk : ∀ sa par ps b, key ≠ .arrow sa par ps b) (hat : name ≠ "at") (hsl : name ≠ "slice")
    (ρ : Eval.Env N) :
    Eval.eval m fuel ρ (.call sp (.member sp' recv name) [key]) =
      (Eval.eval m fuel ρ recv).bind fun r =>
        match r with
        | .regexp re =>
          if name == "test" then do
            let .str input ← Eval.eval m fuel ρ key | none
            return .bool (re.test input)
          else none
        | .map _ | .set _ => (Eval.eval m fuel ρ key).bind (mapMethodVal name r)
        | .list items => (Eval.eval m fuel ρ key).bind fun k => Eval.arrayMethod name items [k]
        | .str s => (Eval.eval m fuel ρ key).bind fun k => Eval.stringMethod name s [k] [Eval.intLiteral? key]
        | _ => none := by
  have hr' : ∀ s, recv ≠ .ident s "Number" := by
    intro s h; subst h; simp [Expr.namesGlobal] at hr
  have hrM : ∀ s, recv ≠ .ident s "Math" := by
    intro s h; subst h; simp [Expr.namesGlobal] at hr
  have hrO : ∀ s, recv ≠ .ident s "Object" := by
    intro s h; subst h; simp [Expr.namesGlobal] at hr
  have hrD : ∀ s, recv ≠ .ident s "Date" := by
    intro s h; subst h; simp [Expr.namesGlobal] at hr
  have hj : ∀ s, recv ≠ .ident s "JSON" := by
    intro s h; subst h; simp [Expr.namesGlobal] at hr
  generalize hR : Eval.eval m fuel ρ recv = r
  rw [Eval.eval]
  all_goals first
    | (rw [hR]
       cases r with
       | none => rfl
       | some v =>
         cases v <;> simp only [Option.bind_some, Option.bind_eq_bind]
         all_goals first
           | rfl
           | (cases Eval.eval m fuel ρ key <;> simp [mapMethodVal]))
    | exact hr'
    | (intro s h; intros; exact absurd h (hrO s))
    | (intro s h; intros; exact absurd h (hj s))
    | exact hrM
    | exact hrO
    | exact hrD
    | (intro _ h _; exact hrD _ h)
    | (intro sa par p b h; exact hk _ _ _ _ h)
    | (intro sa par p q b h; exact hk _ _ _ _ h)
    | (intro h; exact hat h)
    | (intro h; exact hsl h)

/-- What `.ext op args` gives in the output, from the values of its
arguments. -/
theorem out_ext {op : IR.ExprExt} {args : List IR.Expr} {ρ : Eval.Env N} {v : Val N}
    (h : IR.Expr.eval fs fuel ρ (.ext op args) = some v) :
    ∃ vs, IR.Expr.evalList fs fuel ρ args = some vs ∧ IR.ExprExt.apply op vs = some v := by
  simp only [IR.Expr.eval] at h
  cases hl : IR.Expr.evalList fs fuel ρ args with
  | none => simp [hl] at h
  | some vs => simp [hl] at h; exact ⟨vs, rfl, h⟩

/-- `.ext op [r, k]` means `recv.name(key)`, when `r` means `recv`, `k` means
`key`, and `op` gives what the interpreter's method gives. -/
theorem collection_call_sim {env : Translate.Env} {s sp : Span} {recv key : Expr} {name : String}
    {op : IR.ExprExt} {r k : IR.Expr} (hr : recv.namesGlobal = false)
    (hk : ∀ sa par ps b, key ≠ .arrow sa par ps b) (hat : name ≠ "at") (hsl : name ≠ "slice")
    (hrecv : Sim (N := N) m fs fuel env recv r) (hkey : Sim (N := N) m fs fuel env key k)
    (happly : ∀ vr vk w : Val N, IR.ExprExt.apply op [vr, vk] = some w → mapMethodVal name vr vk = some w) :
    Sim (N := N) m fs fuel env (.call s (.member sp recv name) [key]) (.ext op [r, k]) := by
  intro ρs ρo w ha hs hw
  obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
  simp only [IR.Expr.evalList] at hvs
  cases hx : IR.Expr.eval fs fuel ρo r with
  | none => simp [hx] at hvs
  | some vr =>
    cases hy : IR.Expr.eval fs fuel ρo k with
    | none => simp [hx, hy] at hvs
    | some vk =>
      simp [hx, hy] at hvs
      subst hvs
      have hv := happly _ _ _ happ
      rw [eval_mapMethod m fuel _ _ _ _ _ hr hk hat hsl, hrecv ρs ρo _ ha hs hx]
      cases vr <;> simp only [Option.bind_some] <;>
        first
        | (rw [hkey ρs ρo _ ha hs hy]; exact hv)
        | (simp [mapMethodVal] at hv)

theorem mapMethodOf_some {sp : Span} {recv recv' : Expr} {name : String} {op : IR.ExprExt}
    (h : mapMethodOf (.member sp recv name) = some (recv', op)) :
    recv' = recv ∧ ((name = "get" ∧ op = .mapGet) ∨ (name = "has" ∧ op = .mapHas)) := by
  simp only [mapMethodOf] at h
  split at h <;> simp_all

theorem translateMapMethod_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    {env : Translate.Env} {s : Span} {recv : Expr} {op : IR.ExprExt}
    {args : List Expr} {ctx ctx' : Ctx} {c : Code}
    (h : translateMapMethod (F + 1) env s recv op args ctx = .ok c ctx')
    {sp : Span} {name : String} (hname : mapMethodOf (.member sp recv name) = some (recv, op)) :
    Sim (N := N) m fs fuel env (.call s (.member sp recv name) args) c.code := by
  obtain ⟨-, hop⟩ := mapMethodOf_some hname
  simp only [translateMapMethod, ite_state] at h
  split at h
  · simp at h
  rename_i hr
  rcases args with _ | ⟨key, _ | ⟨_, _⟩⟩ <;> simp only at h <;> try (simp at h; done)
  try simp only [pure_bind, ite_state] at h
  split at h
  · simp at h
  rename_i hka
  simp only [Bool.false_eq_true, ↓reduceIte, bind_ok] at h
  obtain ⟨o, s₁, ho, h⟩ := h
  have hrecv := translateRecv_sim m fs fuel (fun _ _ _ hx => ihE _ _ _ _ _ _ hx) ho
  have hrv : Sim (N := N) m fs fuel env recv o.value := fun ρs ρo w ha hs hw =>
    hrecv ρs ρo w ha hs (by rwa [eval_value] at hw)
  have hr' : recv.namesGlobal = false := by simpa using hr
  have hk : ∀ sa par ps b, key ≠ .arrow sa par ps b := fun sa par ps b he => hka _ _ _ _ he
  -- `has` is the method when `op` is `.mapHas`, and `get` otherwise.
  have hasName : (op == .mapHas) = true → name = "has" := fun hhas => by
    rcases hop with ⟨-, rfl⟩ | ⟨h1, -⟩
    · exact absurd hhas (by decide)
    · exact h1
  have getName : ¬(op == .mapHas) = true → name = "get" := fun hhas => by
    rcases hop with ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact h1
    · exact absurd (by decide) hhas
  cases hot : o.type
  all_goals try (simp [hot] at h; done)
  next k v =>
    simp only [hot, bind_ok] at h
    obtain ⟨kc, s₂, hkc, h⟩ := h
    have hkv : Sim (N := N) m fs fuel env key kc.value := fun ρs ρo w ha hs hw =>
      ihE _ _ _ _ _ _ hkc ρs ρo w ha hs (by rwa [eval_value] at hw)
    try simp only [ite_state] at h
    split at h
    rotate_left
    · simp at h
    try simp only [pure_bind, ite_state] at h
    split at h
    · rename_i hhas
      simp at h
      obtain ⟨rfl, -⟩ := h
      obtain rfl := hasName hhas
      refine collection_call_sim m fs fuel hr' hk (by decide) (by decide) hrv hkv fun vr vk w happ => ?_
      cases vr <;> simp [IR.ExprExt.apply] at happ
      obtain ⟨found, hf, rfl⟩ := happ
      simp [mapMethodVal, hf]
    · rename_i hhas
      split at h
      · simp at h
      simp at h
      obtain ⟨rfl, -⟩ := h
      obtain rfl := getName hhas
      refine collection_call_sim m fs fuel hr' hk (by decide) (by decide) hrv hkv fun vr vk w happ => ?_
      cases vr <;> simp [IR.ExprExt.apply] at happ
      obtain ⟨found, hf, rfl⟩ := happ
      simp [mapMethodVal, hf]
  next t =>
    simp only [hot, ite_state] at h
    split at h
    rotate_left
    · simp at h
    rename_i hhas
    simp only [bind_ok] at h
    obtain ⟨xc, s₂, hxc, h⟩ := h
    have hxv : Sim (N := N) m fs fuel env key xc.value := fun ρs ρo w ha hs hw =>
      ihE _ _ _ _ _ _ hxc ρs ρo w ha hs (by rwa [eval_value] at hw)
    try simp only [ite_state] at h
    split at h
    rotate_left
    · simp at h
    simp at h
    obtain ⟨rfl, -⟩ := h
    obtain rfl := hasName hhas
    refine collection_call_sim m fs fuel hr' hk (by decide) (by decide) hrv hxv fun vr vk w happ => ?_
    cases vr <;> (try simp only [IR.ExprExt.apply] at happ) <;> try (simp at happ; done)
    rename_i elems
    simp only [mapMethodVal]
    cases hf : Eval.setHas elems vk <;> simp [hf] at happ ⊢ <;> exact happ

/-- A read of a field, of a member of a string enum, or of the `size` of a map. -/
theorem translateMember_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    {env : Translate.Env} {exp : Option Ty} {sp : Span} {obj : Expr} {name : String} {ctx ctx' : Ctx}
    {c : Code} (h : translateExprCore (F + 1) env exp (.member sp obj name) ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.member sp obj name) c.code := by
  simp only [translateExprCore] at h
  cases he : enumOf? env obj with
  | some e =>
    -- `T.A`: the string of the member, which the interpreter reads from
    -- the object of the enum.
    simp only [he, bind_ok, orReject_ok, pure_ok] at h
    obtain ⟨value, s₁, ⟨hval, rfl⟩, rfl, -⟩ := h
    intro ρs ρo v _ hs hv'
    simp only [IR.Expr.eval, Option.some.injEq] at hv'
    subst hv'
    obtain ⟨sp', n, rfl⟩ : ∃ sp' n, obj = .ident sp' n := by
      cases obj <;> simp [enumOf?] at he; exact ⟨_, _, rfl⟩
    simp only [enumOf?, Bool.or_eq_true] at he
    split at he
    · simp at he
    rename_i hng
    simp only [not_or, Bool.not_eq_true] at hng
    have hname : e.name = n := by simpa using List.find?_some he
    have hres := hs.2.2.1 e (List.mem_of_find?_eq_some he)
    rw [hname] at hres
    have hnone : ρs.lookup n = none := hs.none hng.1
    have hg : n ≠ "NaN" ∧ n ≠ "Infinity" ∧ n ≠ "undefined" := by
      have := hng.2
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> subst h <;> simp [isGlobalName, isNumberName] at this
    simp only [Eval.eval, Expr.optSpine, Bool.false_eq_true, ↓reduceIte, hnone, hres, hg.1, hg.2.1,
      hg.2.2, Option.map_some, Eval.enumObject, Eval.getProp, beq_iff_eq, Option.bind_eq_bind,
      Option.bind_some]
    rw [lookup_map_str hval]
  | none =>
  simp only [he] at h
  split at h
  · rename_i hsp
    cases hc : (Expr.member sp obj name).optChain? with
    | none => simp [hc] at h
    | some bp =>
      obtain ⟨base, path⟩ := bp
      simp only [hc, bind_ok] at h
      obtain ⟨o, s₁, ho, ⟨bind, ty⟩, s₂, -, h⟩ := h
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo v ha hs hv'
      simp only [IR.Expr.eval, IR.Expr.evalList] at hv'
      rw [nullableConditionalReceiver_eval] at hv'
      cases hobj : IR.Expr.eval fs fuel ρo o.code with
      | none => simp [hobj] at hv'
      | some ov =>
        have := ihE _ _ _ _ _ _ ho ρs ρo ov ha hs hobj
        simp only [hobj] at hv'
        rw [eval_member_chain m fuel hsp hc this]
        cases ov <;> simp only [IR.ExprExt.apply] at hv' <;> first | exact hv' | simp at hv'
  rename_i hsp
  simp only [pure_bind, bind_ok] at h
  obtain ⟨o, s₁, ho, h⟩ := h
  have hrecv := translateRecv_sim m fs fuel (fun _ _ _ hx => ihE _ _ _ _ _ _ hx) ho
  simp only [ite_state] at h
  split at h
  · -- `xs.length`: the spec gives the length of the array.
    rename_i hlen
    simp at h
    obtain ⟨rfl, -⟩ := h
    have hn : name = "length" := by simp at hlen; exact hlen.2
    subst hn
    exact length_sound m fs fuel (by simpa using hsp) fun ρs ρo w ha hs hw =>
      hrecv ρs ρo w ha hs (by rwa [eval_value] at hw)
  cases hot : o.type
  case map k v =>
    -- `m.size`, the number of entries.
    simp only [hot, ite_state] at h
    split at h
    · rename_i hsize
      obtain rfl : name = "size" := by simpa using hsize
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo w ha hs hw
      obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
      simp only [IR.Expr.evalList] at hvs
      cases hx : IR.Expr.eval fs fuel ρo o.value with
      | none => simp [hx] at hvs
      | some vo =>
        simp [hx] at hvs
        subst hvs
        rw [eval_value] at hx
        have hobj := hrecv ρs ρo _ ha hs hx
        cases vo <;> (try simp only [IR.ExprExt.apply] at happ) <;> try (simp at happ; done)
        rename_i entries
        simp only [Option.some.injEq] at happ
        subst happ
        simp [Eval.eval, hsp, hobj]
    · simp at h
  case string =>
    -- `s.length`, the number of code units.
    simp only [hot, ite_state] at h
    split at h
    · rename_i hlen
      obtain rfl : name = "length" := by simpa using hlen
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo w ha hs hw
      obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
      simp only [IR.Expr.evalList] at hvs
      cases hx : IR.Expr.eval fs fuel ρo o.value with
      | none => simp [hx] at hvs
      | some vo =>
        simp [hx] at hvs
        subst hvs
        rw [eval_value] at hx
        have hobj := hrecv ρs ρo _ ha hs hx
        cases vo <;> (try simp only [IR.ExprExt.apply] at happ) <;> try (simp at happ; done)
        rename_i str
        simp only [Option.some.injEq] at happ
        subst happ
        simp [Eval.eval, hsp, hobj]
    · simp at h
  case set t =>
    -- `s.size`, the number of elements.
    simp only [hot, ite_state] at h
    split at h
    · rename_i hsize
      obtain rfl : name = "size" := by simpa using hsize
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo w ha hs hw
      obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
      simp only [IR.Expr.evalList] at hvs
      cases hx : IR.Expr.eval fs fuel ρo o.value with
      | none => simp [hx] at hvs
      | some vo =>
        simp [hx] at hvs
        subst hvs
        rw [eval_value] at hx
        have hobj := hrecv ρs ρo _ ha hs hx
        cases vo <;> (try simp only [IR.ExprExt.apply] at happ) <;> try (simp at happ; done)
        rename_i elems
        simp only [Option.some.injEq] at happ
        subst happ
        simp [Eval.eval, hsp, hobj]
    · simp at h
  all_goals try (simp [hot] at h; done)
  all_goals
    simp only [hot] at h
    simp at h
    obtain ⟨_, _, ⟨rfl, rfl⟩, ty, ⟨-, rfl⟩, rfl⟩ := h
    intro ρs ρo v ha hs hv'
    simp only [IR.Expr.eval] at hv'
    cases hobj : IR.Expr.eval fs fuel ρo o.code with
    | none => simp [hobj] at hv'
    | some ov =>
      have := hrecv ρs ρo ov ha hs hobj
      simp only [Eval.eval, hsp, Bool.false_eq_true, ↓reduceIte, this]
      simp only [hobj, Option.bind_eq_bind, Option.bind_some] at hv'
      cases ov <;> simp_all

/-- What the output's loop runs over is what the interpreter's loop visits. -/
theorem loopOver_sim {env : Translate.Env} {iterable : Expr} {items : Code} {elem : Ty}
    {li : IR.Expr} (hsim : Sim (N := N) m fs fuel env iterable items.code)
    (hlo : loopOver items = some (elem, li)) {ρs ρo : Eval.Env N} {vs : List (Val N)}
    (ha : Agree ρs ρo) (hs : Scoped m env ρs) (hi : IR.Expr.eval fs fuel ρo li = some (.list vs)) :
    ∃ v, Eval.eval m fuel ρs iterable = some v ∧ Eval.iterValues v = some vs := by
  unfold loopOver at hlo
  split at hlo <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hlo
  · obtain ⟨-, rfl⟩ := hlo
    exact ⟨_, hsim ρs ρo _ ha hs hi, rfl⟩
  all_goals
    obtain ⟨-, rfl⟩ := hlo
    obtain ⟨ws, hws, happ⟩ := out_ext fs fuel hi
    simp only [IR.Expr.evalList] at hws
    cases hx : IR.Expr.eval fs fuel ρo items.value with
    | none => simp [hx] at hws
    | some w =>
      simp [hx] at hws
      subst hws
      rw [eval_value] at hx
      refine ⟨w, hsim ρs ρo _ ha hs hx, ?_⟩
      cases w <;> simp [IR.ExprExt.apply] at happ
      subst happ
      rfl

/-! ### What a form that iterates visits -/

omit [JSNumber N] in
/-- Without its parentheses, `e` is the call `xs.entries()`. -/
theorem entriesRecv?_some {e recv : Expr} (h : entriesRecv? e = some recv) :
    ∃ sp sp', e.stripParens = .call sp (.member sp' recv "entries") [] := by
  unfold entriesRecv? at h
  split at h
  · cases h; exact ⟨_, _, ‹_›⟩
  · cases h

/-- An iterable other than `xs.entries()` gives what `iterValues` gives for
its value. -/
theorem evalIter_other {e : Expr} (h : entriesRecv? e = none) (ρ : Eval.Env N) :
    Eval.evalIter m fuel ρ e = (Eval.eval m fuel ρ e).bind Eval.iterValues := by
  unfold entriesRecv? at h
  rw [Eval.evalIter]
  split at h
  · cases h
  · rename_i hne
    split
    · rename_i sp sp' recv heq; exact absurd heq (hne sp sp' recv)
    · rfl

/-- `xs.entries()`, in any number of parentheses, gives each element of an
array with its index, and the entries of a map. -/
theorem evalIter_entries {e recv : Expr} (h : entriesRecv? e = some recv) (ρ : Eval.Env N) :
    Eval.evalIter m fuel ρ e =
      (Eval.eval m fuel ρ recv).bind fun
        | .list items => some (Eval.entriesOf items)
        | .map es => Eval.iterValues (.map es)
        | _ => none := by
  obtain ⟨sp, sp', hs⟩ := entriesRecv?_some h
  rw [Eval.evalIter]
  split
  · rename_i sp₁ sp₁' recv' heq
    rw [hs] at heq
    cases heq
    generalize Eval.eval m fuel ρ recv = r
    cases r with
    | none => rfl
    | some w => cases w <;> rfl
  · rename_i hne
    exact absurd hs (hne sp sp' recv)

/-- What a form that iterates `iterable` visits in the output, when `iterOf`
found `found`, is what the interpreter's `evalIter` visits. -/
def IterSim (env : Translate.Env) (iterable : Expr) (found : Option (Ty × IR.Expr)) : Prop :=
  ∀ t li, found = some (t, li) → ∀ (ρs ρo : Eval.Env N) vs, Agree ρs ρo → Scoped m env ρs →
    IR.Expr.eval fs fuel ρo li = some (.list vs) → Eval.evalIter m fuel ρs iterable = some vs

theorem iterOf_sim {env : Translate.Env} {trItems trRecv : Expr → TM Code} {iterable : Expr}
    (hI : ∀ ctx c ctx', trItems iterable ctx = .ok c ctx' → Sim (N := N) m fs fuel env iterable c.code)
    (hR : ∀ e ctx c ctx', trRecv e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    {ctx ctx' : Ctx} {found : Option (Ty × IR.Expr)} (h : iterOf trItems trRecv iterable ctx = .ok found ctx') :
    IterSim (N := N) m fs fuel env iterable found := by
  unfold iterOf at h
  cases he : entriesRecv? iterable with
  | none =>
    simp only [he, bind_ok, pure_ok] at h
    obtain ⟨items, s₁, hitems, rfl, -⟩ := h
    intro t li hlo ρs ρo vs ha hs hi
    obtain ⟨v, hv, hiter⟩ := loopOver_sim m fs fuel (hI _ _ _ hitems) hlo ha hs hi
    rw [evalIter_other m fuel he, hv]
    simpa using hiter
  | some recv =>
    simp only [he, bind_ok] at h
    obtain ⟨xs, s₁, hxs, h⟩ := h
    have hsim := hR _ _ _ _ hxs
    intro t li hfound ρs ρo vs ha hs hi
    rw [evalIter_entries m fuel he]
    generalize hty : xs.type = ty at h
    cases ty
    case array elem =>
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at hfound
      obtain ⟨-, rfl⟩ := hfound
      obtain ⟨ws, hws, happ⟩ := out_ext fs fuel hi
      simp only [IR.Expr.evalList] at hws
      cases hx : IR.Expr.eval fs fuel ρo xs.value with
      | none => simp [hx] at hws
      | some w =>
        simp [hx] at hws
        subst hws
        rw [eval_value] at hx
        rw [hsim ρs ρo _ ha hs hx]
        cases w <;> simp [IR.ExprExt.apply] at happ
        subst happ
        rfl
    case map k v =>
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      simp only [loopOver, hty, Option.some.injEq, Prod.mk.injEq] at hfound
      obtain ⟨-, rfl⟩ := hfound
      obtain ⟨ws, hws, happ⟩ := out_ext fs fuel hi
      simp only [IR.Expr.evalList] at hws
      cases hx : IR.Expr.eval fs fuel ρo xs.value with
      | none => simp [hx] at hws
      | some w =>
        simp [hx] at hws
        subst hws
        rw [eval_value] at hx
        rw [hsim ρs ρo _ ha hs hx]
        cases w <;> simp [IR.ExprExt.apply] at happ
        subst happ
        rfl
    all_goals
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      simp at hfound

/-! ### Array spread -/

/-- What a piece of an array literal stands for: an element that is not a
spread, which its code means, or a spread `...x`, whose list is what
`evalIter` visits in `x`. -/
def PartSim (env : Translate.Env) (e : Expr) : ElemPart → Prop
  | .one c => e.spreadArg? = none ∧ Sim (N := N) m fs fuel env e c.code
  | .many t li => ∃ sp x, e = .spread sp x ∧ IterSim (N := N) m fs fuel env x (some (t, li))

theorem spreadArg?_some {e x : Expr} {sp : Span} (h : e.spreadArg? = some (sp, x)) :
    e = .spread sp x := by
  cases e <;> simp [Expr.spreadArg?] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem translateElem_sim {env : Translate.Env} {tr : Option Ty → Expr → TM Code}
    (htr : ∀ exp e ctx c ctx', tr exp e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    {exp : Option Ty} {e : Expr} {ctx ctx' : Ctx} {p : ElemPart}
    (h : translateElem tr exp e ctx = .ok p ctx') : PartSim (N := N) m fs fuel env e p := by
  unfold translateElem at h
  cases hs : e.spreadArg? with
  | some q =>
    obtain ⟨sp, x⟩ := q
    rw [hs] at h
    simp only [bind_ok, orReject_ok, pure_ok] at h
    obtain ⟨found, s₁, hi, ⟨t, li⟩, s₂, ⟨rfl, -⟩, rfl, -⟩ := h
    exact ⟨sp, x, spreadArg?_some hs,
      iterOf_sim m fs fuel (fun _ _ _ he => htr _ _ _ _ _ he) (fun _ _ _ _ he => htr _ _ _ _ _ he) hi⟩
  | none =>
    rw [hs] at h
    simp only [bind_ok, pure_ok] at h
    obtain ⟨c, s₁, hc, rfl, -⟩ := h
    exact ⟨hs, htr _ _ _ _ _ hc⟩

/-- The lists that the output joins hold, one after another, what the array
literal holds. -/
theorem mapM_parts_sim {env : Translate.Env} {f : Expr → TM ElemPart}
    (hf : ∀ e ctx p ctx', f e ctx = .ok p ctx' → PartSim (N := N) m fs fuel env e p)
    (unions : List UnionInfo) (t : Ty) :
    ∀ (es : List Expr) (ctx : Ctx) (ps : List ElemPart) (ctx' : Ctx),
      es.mapM f ctx = .ok ps ctx' →
      ∀ (ρs ρo : Eval.Env N) ws lss, Agree ρs ρo → Scoped m env ρs →
        IR.Expr.evalList fs fuel ρo (partLists unions t ps) = some ws → ws.mapM IR.listItems? = some lss →
        Eval.evalElems m fuel ρs es = some lss.flatten := by
  intro es
  induction es with
  | nil =>
    intro ctx ps ctx' h ρs ρo ws lss _ _ hws hl
    simp [List.mapM_nil] at h
    obtain ⟨rfl, -⟩ := h
    simp [partLists, IR.Expr.evalList] at hws
    subst hws
    simp at hl
    subst hl
    simp [Eval.evalElems]
  | cons e es ih =>
    intro ctx ps ctx' h ρs ρo ws lss ha hs hws hl
    simp [List.mapM_cons] at h
    obtain ⟨p, s₁, hp, ps', hps, rfl⟩ := h
    have hpart := hf _ _ _ _ hp
    cases p with
    | many t' li =>
      obtain ⟨sp, x, rfl, hit⟩ := hpart
      simp only [partLists, IR.Expr.evalList] at hws
      cases hw : IR.Expr.eval fs fuel ρo li with
      | none => simp [hw] at hws
      | some w =>
        cases hws' : IR.Expr.evalList fs fuel ρo (partLists unions t ps') with
        | none => simp [hw, hws'] at hws
        | some ws' =>
          simp [hw, hws'] at hws
          subst hws
          cases w with
          | list l =>
            cases hl' : ws'.mapM IR.listItems? with
            | none => simp [List.mapM_cons, IR.listItems?, hl'] at hl
            | some lss' =>
              simp [List.mapM_cons, IR.listItems?, hl'] at hl
              subst hl
              have hiter := hit _ _ rfl ρs ρo l ha hs hw
              have := ih _ _ _ hps ρs ρo ws' lss' ha hs hws' hl'
              simp [Eval.evalElems, hiter, this]
          | _ => simp [List.mapM_cons, IR.listItems?] at hl
    | one c =>
      obtain ⟨hsp, hsim⟩ := hpart
      simp only [partLists] at hws
      split at hws
      · next xs ty rest heq =>
        simp only [IR.Expr.evalList, IR.Expr.eval, eval_into_value] at hws
        cases hv0 : IR.Expr.eval fs fuel ρo c.value with
        | none => simp [hv0] at hws
        | some v0 =>
          cases hxs : IR.Expr.evalList fs fuel ρo xs with
          | none => simp [hv0, hxs] at hws
          | some vxs =>
            cases hrest : IR.Expr.evalList fs fuel ρo rest with
            | none => simp [hv0, hxs, hrest] at hws
            | some ws' =>
              simp [hv0, hxs, hrest] at hws
              subst hws
              cases hl' : ws'.mapM IR.listItems? with
              | none => simp [List.mapM_cons, IR.listItems?, hl'] at hl
              | some lss' =>
                simp [List.mapM_cons, IR.listItems?, hl'] at hl
                subst hl
                have hev : IR.Expr.evalList fs fuel ρo (partLists unions t ps') = some (.list vxs :: ws') := by
                  simp [heq, IR.Expr.evalList, IR.Expr.eval, hxs, hrest]
                have hm : (Val.list vxs :: ws').mapM IR.listItems? = some (vxs :: lss') := by
                  simp [List.mapM_cons, IR.listItems?, hl']
                have := ih _ _ _ hps ρs ρo _ _ ha hs hev hm
                rw [eval_value] at hv0
                rw [evalElems_cons m fuel hsp, hsim ρs ρo _ ha hs hv0, this]
                simp
      · simp only [IR.Expr.evalList, IR.Expr.eval, eval_into_value] at hws
        cases hv0 : IR.Expr.eval fs fuel ρo c.value with
        | none => simp [hv0] at hws
        | some v0 =>
          cases hws' : IR.Expr.evalList fs fuel ρo (partLists unions t ps') with
          | none => simp [hv0, hws'] at hws
          | some ws' =>
            simp [hv0, hws'] at hws
            subst hws
            cases hl' : ws'.mapM IR.listItems? with
            | none => simp [List.mapM_cons, IR.listItems?, hl'] at hl
            | some lss' =>
              simp [List.mapM_cons, IR.listItems?, hl'] at hl
              subst hl
              have := ih _ _ _ hps ρs ρo _ _ ha hs hws' hl'
              rw [eval_value] at hv0
              rw [evalElems_cons m fuel hsp, hsim ρs ρo _ ha hs hv0, this]
              simp

/-- An array literal with a spread means the lists that the output joins. -/
theorem translateSpreadArray_sound {env : Translate.Env} {tr : Option Ty → Expr → TM Code}
    (htr : ∀ exp e ctx c ctx', tr exp e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    {exp : Option Ty} {s : Span} {elems : List Expr} {ctx ctx' : Ctx} {c : Code}
    (h : translateSpreadArray tr exp s elems ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.array s elems) c.code := by
  simp only [translateSpreadArray, bind_ok, pure_ok, get_ok] at h
  obtain ⟨parts, s₁, hparts, elem, s₂, -, _, s₃, -, unions, _, ⟨-, -⟩, hcode, -⟩ := h
  rw [← hcode]
  intro ρs ρo v ha hs hv
  obtain ⟨ws, hws, happ⟩ := out_ext fs fuel hv
  simp only [IR.ExprExt.apply] at happ
  cases hm : ws.mapM IR.listItems? with
  | none => simp [hm] at happ
  | some lss =>
    simp [hm] at happ
    subst happ
    have := mapM_parts_sim m fs fuel (fun _ _ _ _ hp => translateElem_sim m fs fuel htr hp) unions.unions elem
      elems ctx parts s₁ hparts ρs ρo ws lss ha hs hws hm
    simp [Eval.eval, this]

/-- `new Date(t)` means what the interpreter's rule for it means: the date
whose time value is TimeClip of `t`. -/
private theorem hasHoistedMark_false_of_no_mark {typeArgs : List TypeExpr}
    (h : ∀ span, typeArgs ≠ [.keyword span "'"]) : Eval.hasHoistedMark typeArgs = false := by
  cases typeArgs with
  | nil => simp [Eval.hasHoistedMark]
  | cons t rest =>
    cases rest with
    | cons _ _ => simp [Eval.hasHoistedMark]
    | nil =>
      cases t with
      | keyword span name =>
        by_cases hn : name = "'"
        · exact False.elim (h span (by simp [hn]))
        · simp [Eval.hasHoistedMark]
      | _ => simp [Eval.hasHoistedMark]

theorem translateNewDate_sound {tr : Option Ty → Expr → TM Code} {env : Translate.Env}
    (htr : ∀ exp e ctx c ctx', tr exp e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    {sp : Span} {typeArgs : List TypeExpr} {args : List Expr} {ctx ctx' : Ctx} {c : Code}
    (htypeArgs : typeArgs = [])
    (h : translateNewDate tr env sp args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.new sp "Date" typeArgs args) c.code := by
  match args, h with
  | [arg], h =>
    unfold translateNewDate at h
    split at h
    · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at h
    rename_i hhas
    simp only [pure_bind, bind_ok] at h
    obtain ⟨t, s₁, ht, h⟩ := h
    split at h
    · simp at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo v ha hs hv
      obtain ⟨x, hx, rfl⟩ := out_dateOfNumber fs fuel hv
      rw [eval_value] at hx
      have harg := htr _ _ _ _ _ ht ρs ρo _ ha hs hx
      subst typeArgs
      have hmark : Eval.hasHoistedMark [] = false := rfl
      have hclassnone := hs.2.2.2.2 "Date" (by decide)
      simp [Eval.eval, hmark, hclassnone, hs.none (by simpa using hhas), harg]
    · simp at h
  | [], h =>
    unfold translateNewDate at h
    split at h <;> simp only [bind_ok, pure_bind, reject_ne_ok, false_and, exists_false] at h
  | _ :: _ :: _, h =>
    unfold translateNewDate at h
    split at h <;> simp only [bind_ok, pure_bind, reject_ne_ok, false_and, exists_false] at h

/-- `new Map()` and `new Set()`, and `new Map(items)` and `new Set(items)`,
which set or add each value that `items` visits. -/
theorem translateNew_sound {tr : Option Ty → Expr → TM Code} {env : Translate.Env}
    (htr : ∀ exp e ctx c ctx', tr exp e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    {exp : Option Ty} {sp : Span} {callee : String} {typeArgs : List TypeExpr} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code}
    (h : translateNew tr env exp sp callee typeArgs args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.new sp callee typeArgs args) c.code := by
  unfold translateNew at h
  split at h
  · rename_i hc
    obtain rfl : callee = "Date" := by simpa using hc
    split at h
    · rename_i htypeArgs
      exact translateNewDate_sound m fs fuel htr (by simpa using htypeArgs) h
    · simp at h
  simp only [ite_state] at h
  split at h
  rotate_left
  · simp at h
  rename_i hcallee
  simp only [pure_bind, ite_state] at h
  split at h
  · simp at h
  rename_i hhas
  try simp only [pure_bind] at h
  have hnone : ∀ ρs : Eval.Env N, Scoped m env ρs → ρs.lookup callee = none :=
    fun ρs hs => hs.none (by simpa using hhas)
  have hc : callee = "Map" ∨ callee = "Set" := by simpa using hcallee
  rcases hc with rfl | rfl
  · simp only [show ("Map" == "Map") = true from rfl, ↓reduceIte] at h
    rcases args with _ | ⟨arg, _ | ⟨_, _⟩⟩
    · simp only [bind_ok] at h
      obtain ⟨type, s₁, htype, h⟩ := h
      have hnot : ∀ span, typeArgs ≠ [.keyword span "'"] := by
        intro span hmark
        subst typeArgs
        simp [Translate.newMapType] at htype
      have hmark := hasHoistedMark_false_of_no_mark hnot
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo v _ hs hv
      simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] at hv
      subst hv
      have hclassnone := hs.2.2.2.2 "Map" (by decide)
      simp [Eval.eval, hmark, hnone ρs hs, hclassnone]
    · simp only [bind_ok, orReject_ok] at h
      obtain ⟨declared, s₁, hdeclared, found, s₂, hfound, ⟨elem, li⟩, s₃, ⟨rfl, rfl⟩, type, s₄, -, h⟩ := h
      have hnot : ∀ span, typeArgs ≠ [.keyword span "'"] := by
        intro span hmark
        subst typeArgs
        simp [Translate.declaredMapType] at hdeclared
      have hmark := hasHoistedMark_false_of_no_mark hnot
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      have hit := iterOf_sim m fs fuel
        (fun _ _ _ hx => translateRecv_sim m fs fuel (fun _ _ _ hx => htr _ _ _ _ _ hx) hx)
        (fun _ _ _ _ hx => translateRecv_sim m fs fuel (fun _ _ _ hx => htr _ _ _ _ _ hx) hx) hfound
      intro ρs ρo v ha hs hv
      simp only [IR.Expr.eval] at hv
      cases hli : IR.Expr.eval fs fuel ρo li with
      | none => simp [IR.Expr.evalList, hli] at hv
      | some u =>
        simp [IR.Expr.evalList, hli] at hv
        cases u <;> simp [IR.ExprExt.apply] at hv
        rename_i vs
        obtain ⟨es, hes, rfl⟩ := hv
        have hiter := hit _ _ rfl ρs ρo _ ha hs hli
        have hclassnone := hs.2.2.2.2 "Map" (by decide)
        simp [Eval.eval, hmark, hnone ρs hs, hclassnone, hiter, hes]
    · simp at h
  · simp only [show ("Set" == "Map") = false from rfl, ↓reduceIte, Bool.false_eq_true] at h
    rcases args with _ | ⟨arg, _ | ⟨_, _⟩⟩
    · simp only [bind_ok] at h
      obtain ⟨type, s₁, htype, h⟩ := h
      have hnot : ∀ span, typeArgs ≠ [.keyword span "'"] := by
        intro span hmark
        subst typeArgs
        simp [Translate.newSetType, Translate.unsupportedType, reject_ne_ok] at htype
      have hmark := hasHoistedMark_false_of_no_mark hnot
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo v _ hs hv
      simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] at hv
      subst hv
      have hclassnone := hs.2.2.2.2 "Set" (by decide)
      simp [Eval.eval, hmark, hnone ρs hs, hclassnone]
    · simp only [bind_ok, orReject_ok] at h
      obtain ⟨declared, s₁, hdeclared, found, s₂, hfound, ⟨elem, li⟩, s₃, ⟨rfl, rfl⟩, type, s₄, -, h⟩ := h
      have hnot : ∀ span, typeArgs ≠ [.keyword span "'"] := by
        intro span hmark
        subst typeArgs
        simp [Translate.declaredSetType, Translate.unsupportedType, reject_ne_ok] at hdeclared
      have hmark := hasHoistedMark_false_of_no_mark hnot
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      have hit := iterOf_sim m fs fuel
        (fun _ _ _ hx => translateRecv_sim m fs fuel (fun _ _ _ hx => htr _ _ _ _ _ hx) hx)
        (fun _ _ _ _ hx => translateRecv_sim m fs fuel (fun _ _ _ hx => htr _ _ _ _ _ hx) hx) hfound
      intro ρs ρo v ha hs hv
      simp only [IR.Expr.eval] at hv
      cases hli : IR.Expr.eval fs fuel ρo li with
      | none => simp [IR.Expr.evalList, hli] at hv
      | some u =>
        simp [IR.Expr.evalList, hli] at hv
        cases u <;> simp [IR.ExprExt.apply] at hv
        rename_i vs
        obtain ⟨es, hes, rfl⟩ := hv
        have hiter := hit _ _ rfl ρs ρo _ ha hs hli
        have hclassnone := hs.2.2.2.2 "Set" (by decide)
        simp [Eval.eval, hmark, hnone ρs hs, hclassnone, hiter, hes]
    · simp at h

theorem out_numberSameValue {a b : IR.Expr} {ρ : Eval.Env N} {v : Val N}
    (h : IR.Expr.eval fs fuel ρ (.ext .numberSameValue [a, b]) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.num x) ∧ IR.Expr.eval fs fuel ρ b = some (.num y) ∧
      v = .bool (JSNumber.sameValue x y) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => simp [hx, hy] at h
    | some u =>
      simp only [hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      cases w <;> cases u <;> simp [IR.ExprExt.apply] at h
      exact ⟨_, _, rfl, rfl, h.symm⟩

theorem out_numberOfInt {a : IR.Expr} {ρ : Eval.Env N} {v : Val N}
    (h : IR.Expr.eval fs fuel ρ (.ext .numberOfInt [a]) = some v) :
    ∃ i, IR.Expr.eval fs fuel ρ a = some (.int i) ∧ v = .num (JSNumber.ofInt i) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx, IR.ExprExt.apply] at h
  | some w => cases w <;> simp_all [IR.ExprExt.apply]

/-- The interpreter's rule for `Object.is(a, b)`, where no variable hides
`Object`: SameValue of the values of the arguments. -/
theorem eval_objectIs (sp sp' sp'' : Span) (x y : Expr) (ρ : Eval.Env N)
    (hnone : ρ.lookup "Object" = none) :
    Eval.eval m fuel ρ (.call sp (.member sp' (.ident sp'' "Object") "is") [x, y]) =
      (Eval.eval m fuel ρ x).bind fun p => (Eval.eval m fuel ρ y).bind fun q =>
        (Eval.sameValue p q).map .bool := by
  rw [Eval.eval]
  · simp only [hnone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    cases Eval.eval m fuel ρ x <;> cases Eval.eval m fuel ρ y <;> simp
    rename_i p q
    cases Eval.sameValue p q <;> rfl
  all_goals simp

/-- Two values that the output compares with `=` are the same by SameValue
when they are equal. -/
theorem sameValue_of_eqVal {p q : Val N} {t : Bool} (h : IR.eqVal p q = some t) :
    Eval.sameValue p q = some t := by
  unfold IR.eqVal at h
  split at h <;> simp_all [Eval.sameValue, Eval.strictEq]

/-- `translateObjectIs` means what the interpreter's rule for `Object.is`
means, when `tr` means what each argument means. Its code is no call. -/
theorem translateObjectIs_sound {tr : Expr → TM Code} {env : Translate.Env}
    (htr : ∀ e ctx c ctx', tr e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    (hO : env.has "Object" = false) {sp sp' sp'' : Span} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code} (h : translateObjectIs tr sp args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.call sp (.member sp' (.ident sp'' "Object") "is") args) c.code ∧
      ∀ ref outs, c.code ≠ .call ref outs := by
  unfold translateObjectIs at h
  match args, h with
  | [x, y], h =>
    simp at h
    obtain ⟨a, s₁, hta, b, s₂, htb, h⟩ := h
    split at h
    · simp at h
      obtain ⟨rfl, -⟩ := h
      refine ⟨fun ρs ρo v ha hs hv => ?_, by intro ref outs hc; cases hc⟩
      obtain ⟨p, q, hp, hq, rfl⟩ := out_numberSameValue fs fuel hv
      rw [eval_value] at hp hq
      rw [eval_objectIs m fuel _ _ _ _ _ _ (hs.none hO), htr _ _ _ _ hta ρs ρo _ ha hs hp,
        htr _ _ _ _ htb ρs ρo _ ha hs hq]
      simp [Eval.sameValue]
    · split at h
      · simp at h
        obtain ⟨rfl, -⟩ := h
        refine ⟨fun ρs ρo v ha hs hv => ?_, by intro ref outs hc; cases hc⟩
        obtain ⟨p, q, t, hp, hq, ht, rfl⟩ := out_eq fs fuel hv
        rw [eval_value] at hp hq
        rw [eval_objectIs m fuel _ _ _ _ _ _ (hs.none hO), htr _ _ _ _ hta ρs ρo _ ha hs hp,
          htr _ _ _ _ htb ρs ρo _ ha hs hq]
        simp [sameValue_of_eqVal ht]
      · simp at h
  | [], h => simp at h
  | [_], h => simp at h
  | _ :: _ :: _ :: _, h => simp at h

/-- Dictionary keys, entries and ownership tests read only own properties.
Each translated argument agrees with the source before the operation runs. -/
theorem translateDictionaryCall_sound {tr : Expr → TM Code} {env : Translate.Env}
    (htr : ∀ e ctx c ctx', tr e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    (hO : env.has "Object" = false) {sp sp' sp'' : Span} {method : String} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code} (h : translateDictionaryCall tr sp method args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.call sp (.member sp' (.ident sp'' "Object") method) args) c.code ∧
      ∀ ref outs, c.code ≠ .call ref outs := by
  unfold translateDictionaryCall at h
  cases args with
  | nil => simp at h
  | cons obj rest =>
    simp only [bind_ok] at h
    obtain ⟨record, s₁, hr, h⟩ := h
    match record.type, h with
    | .struct ref [value], h =>
      simp only [ite_state] at h
      split at h
      · simp only [pure_bind] at h
        split at h
        · simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          refine ⟨?_, fun ref outs hc => by cases hc⟩
          intro ρs ρo v ha hs hv
          simp only [IR.Expr.eval, IR.Expr.evalList] at hv
          cases he : IR.Expr.eval fs fuel ρo record.value with
          | none => simp [he] at hv
          | some rv =>
            cases rv <;> simp [he, IR.ExprExt.apply] at hv
            rename_i fields
            have ho := htr _ _ _ _ hr ρs ρo (.obj fields) ha hs (by rwa [eval_value] at he)
            simp [Eval.eval, hs.none hO, ho, ← hv]
        · simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          refine ⟨?_, fun ref outs hc => by cases hc⟩
          intro ρs ρo v ha hs hv
          simp only [IR.Expr.eval, IR.Expr.evalList] at hv
          cases he : IR.Expr.eval fs fuel ρo record.value with
          | none => simp [he] at hv
          | some rv =>
            cases rv <;> simp [he, IR.ExprExt.apply] at hv
            rename_i fields
            have ho := htr _ _ _ _ hr ρs ρo (.obj fields) ha hs (by rwa [eval_value] at he)
            simp [Eval.eval, hs.none hO, ho, ← hv]
        · simp only [bind_ok, requireFeature_ok] at h
          obtain ⟨_, _, ⟨-, rfl⟩, keyCode, s₂, hk, h⟩ := h
          split at h
          · simp only [pure_ok] at h
            obtain ⟨rfl, -⟩ := h
            refine ⟨?_, fun ref outs hc => by cases hc⟩
            intro ρs ρo v ha hs hv
            simp only [IR.Expr.eval, IR.Expr.evalList] at hv
            cases he : IR.Expr.eval fs fuel ρo record.value with
            | none => simp [he] at hv
            | some rv =>
              cases hke : IR.Expr.eval fs fuel ρo keyCode.value with
              | none => simp [he, hke] at hv
              | some kv =>
                cases rv <;> simp [he, hke, IR.ExprExt.apply] at hv
                cases kv <;> simp at hv
                rename_i fields key
                have ho := htr _ _ _ _ hr ρs ρo (.obj fields) ha hs (by rwa [eval_value] at he)
                have hkey := htr _ _ _ _ hk ρs ρo (.str key) ha hs (by rwa [eval_value] at hke)
                simp [Eval.eval, hs.none hO, ho, hkey, ← hv]
          · simp at h
        · simp at h
      · simp at h
    | .struct _ [], h | .struct _ (_ :: _ :: _), h => simp at h
    | .bigint, h | .number, h | .boolean, h | .string, h | .null, h
      | .nullable _, h | .optional _, h | .array _, h | .enum _, h
      | .tagged .., h | .literal _, h | .tuple _, h | .param _, h
      | .map .., h | .set _, h | .date, h | .regexp, h => simp at h

/-- `translateNumberCall` means what the interpreter's rule for `Number(b)`
means, when `tr` means what the argument means. Its code is no call. -/
theorem translateNumberCall_sound {tr : Expr → TM Code} {env : Translate.Env}
    (htr : ∀ e ctx c ctx', tr e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    (hN : env.has "Number" = false) {sp sp' : Span} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code} (h : translateNumberCall tr sp args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.call sp (.ident sp' "Number") args) c.code ∧
      ∀ ref outs, c.code ≠ .call ref outs := by
  unfold translateNumberCall at h
  match args, h with
  | [x], h =>
    simp at h
    obtain ⟨a, s₁, hta, h⟩ := h
    split at h
    · simp at h
      obtain ⟨rfl, -⟩ := h
      refine ⟨fun ρs ρo v ha hs hv => ?_, by intro ref outs hc; cases hc⟩
      obtain ⟨i, hi, rfl⟩ := out_numberOfInt fs fuel hv
      rw [eval_value] at hi
      have harg := htr _ _ _ _ hta ρs ρo _ ha hs hi
      rw [eval_call_toOption, Eval.evalCall]
      simp [Eval.evalList, harg, hs.none hN, Eval.numberOf, Except.toOption]
    · simp at h
  | [], h => simp at h
  | _ :: _ :: _, h => simp at h

/-- The interpreter's rule for `Math.f(args)`, where no variable hides `Math`:
the function of `mathCall` on the values of the arguments. -/
theorem eval_math (sp sp' sp'' : Span) (f : String) (args : List Expr) (ρ : Eval.Env N)
    (hnone : ρ.lookup "Math" = none) :
    Eval.eval m fuel ρ (.call sp (.member sp' (.ident sp'' "Math") f) args) =
      (Eval.evalList m fuel ρ args).bind (Eval.mathCall f) := by
  rw [Eval.eval]
  · simp [hnone]
  all_goals simp

/-- `translateMathCall` means what the interpreter's rule for `Math.f(args)`
means, when `tr` means what each argument means, and its code is an
operation of the number model. -/
theorem translateMathCall_sound {tr : Expr → TM Code} {env : Translate.Env}
    (htr : ∀ e ctx c ctx', tr e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    (hM : env.has "Math" = false) {sp sp' sp'' : Span} {f : String} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code} (h : translateMathCall tr sp f args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.call sp (.member sp' (.ident sp'' "Math") f) args) c.code ∧
      ∃ op outs, c.code = .ext op outs := by
  unfold translateMathCall at h
  cases hfn : numberFn? f with
  | some fn =>
    simp only [hfn] at h
    match args, h with
    | [arg], h =>
      simp at h
      obtain ⟨a, s₁, hta, h⟩ := h
      split at h
      · simp at h
        obtain ⟨hcode, -⟩ := h
        refine ⟨fun ρs ρo v ha hs hv => ?_, _, _, by rw [← hcode]⟩
        rw [← hcode] at hv
        obtain ⟨n, hn, rfl⟩ := out_numberFn fs fuel hv
        rw [eval_value] at hn
        have harg := htr _ _ _ _ hta ρs ρo _ ha hs hn
        rw [eval_math m fuel _ _ _ _ _ _ (hs.none hM)]
        unfold numberFn? at hfn
        split at hfn <;> cases hfn <;>
          simp [Eval.evalList, harg, Eval.mathCall, IR.NumberFn.apply]
      · simp at h
    | [], h => simp at h
    | _ :: _ :: _, h => simp at h
  | none =>
    simp only [hfn] at h
    simp at h
    split at h
    · rename_i hf
      simp at h
      obtain ⟨codes, s₁, hcodes, -, hcode⟩ := h
      have hargs := mapM_sim m fs fuel htr args ctx codes s₁ hcodes
      refine ⟨fun ρs ρo v ha hs hv => ?_, _, _, by rw [← hcode]⟩
      rw [← hcode] at hv
      obtain ⟨vs, xs, hvs, hxs, rfl⟩ := out_numberFold fs fuel hv
      rw [eval_math m fuel _ _ _ _ _ _ (hs.none hM), hargs ρs ρo vs ha hs hvs]
      rcases hf with rfl | rfl <;> simp [Eval.mathCall, hxs]
    · simp at h

/-- A call of a function of the program: the output's call means what the
source's call means, and it returns or throws what the source's call returns
or throws (`CallSim`). -/
theorem translateCall_sound {F : Nat} (hc : CallsAgree (N := N) m.program fs fuel)
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code) :
    ∀ env sp callee args top ctx c ctx', translateCall (F + 1) env sp callee args top ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.call sp callee args) c.code ∧
        CallSim (N := N) m fs fuel env callee args c.code := by
  intro env sp callee args top ctx c ctx' h
  simp only [translateCall] at h
  cases callee <;> simp at h
  case ident sp' name =>
    by_cases hN : name = "Number"
    · subst hN
      simp at h
      cases hNb : env.has "Number" <;> simp [hNb] at h
      obtain ⟨hsim, hnc⟩ :=
        translateNumberCall_sound m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h) hNb h
      exact ⟨hsim, fun ref outs' hout => absurd hout (hnc ref outs')⟩
    simp [hN] at h
    split at h
    · simp at h
    · simp at h
      obtain ⟨fn, s₁, ⟨hfind, rfl⟩, h⟩ := h
      split at h
      · simp at h
      · rename_i hlocal
        have hlocal' : env.has name = false := by simpa using hlocal
        try simp only [bind_ok] at h
        obtain ⟨_, s₂, hcf, h⟩ := h
        obtain rfl := checkCrossFileThrow_ok hcf
        try simp only [bind_ok] at h
        obtain ⟨_, s₂, hck, h⟩ := h
        obtain rfl := checkThrowingCall_ok hck
        split at h
        · next hlen =>
          have hle : args.length ≤ fn.params.length := by
            first | exact hlen.1 | (simp at hlen; exact hlen.1)
          -- The arguments, then the checks of their types, which do not
          -- change what the call means.
          simp only [bind_ok] at h
          -- Fixing the type of an `undefined` argument keeps its value.
          obtain ⟨first, s₂, hcodes, _, s₃, -, _, s₄, -, h⟩ := h
          obtain ⟨_, s₁, _, h⟩ := h
          obtain ⟨unions, hget, hresult⟩ := map_ok.mp h
          have hget' : unions = s₁ ∧ ctx' = s₁ := by
            simpa only [get_ok, EStateM.Result.ok.injEq] using hget
          obtain ⟨rfl, rfl⟩ := hget'
          let codes := fixArgs fn.params first
          let sol := Ty.unifyList [] fn.params (codes.map (·.type))
          have hcode : c.code = .call fn.ref (optArgs ctx'.unions sol codes fn.params ++
              List.drop args.length (fn.params.map fun param =>
                if param matches .optional (.nullable _) then IR.Expr.nullishUndefined else IR.Expr.undefined)) := by
            simpa [codes, sol] using (congrArg Code.code hresult).symm
          -- What the call returns or throws, from which its value follows.
          have hcall : ∀ (ρs ρo : Eval.Env N) r, Agree ρs ρo → Scoped m env ρs →
              IR.Expr.evalCall fs fuel ρo fn.ref (optArgs ctx'.unions sol codes fn.params ++
                List.drop args.length (fn.params.map fun param =>
                  if param matches .optional (.nullable _) then IR.Expr.nullishUndefined else IR.Expr.undefined)) = some r →
              Eval.evalCall m fuel ρs name args = some r := by
            intro ρs ρo r ha hs hr
            have hmissing : ∀ e, e ∈ (fn.params.drop args.length).map (fun param =>
                if param matches .optional (.nullable _) then IR.Expr.nullishUndefined else IR.Expr.undefined) →
                IR.Expr.eval fs fuel ρo e = some .undefined := by
              intro e he
              obtain ⟨param, hp, rfl⟩ := List.mem_map.mp he
              split <;> simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply]
            rw [out_evalCall, ← List.map_drop] at hr
            rw [evalList_append_undefined fs fuel ρo _ hmissing, evalList_optArgs] at hr
            rw [fixArgs_value] at hr
            cases hx : IR.Expr.evalList fs fuel ρo (first.map Code.value) with
            | none => simp [hx] at hr
            | some vs =>
              simp only [hx] at hr
              have hargs := zip_sim_value m fs fuel ?hg args fn.params _ first _ hle hcodes
                ρs ρo vs ha hs hx
              · have hname : fn.name = name := by simpa using List.find?_some hfind
                have hres := (hs.2.1 fn (List.mem_of_find?_eq_some hfind)).1
                rw [hname] at hres
                rw [evalCall_eq (hn := hN) (hl := hs.none hlocal'), hargs]
                simp only [Option.bind_some, hres, callS_append_undefined (hc _ _ _ hr)]
              case hg =>
                intro x t c₀ o c₁ hgo
                intro ρs' ρo' w ha' hs' hw
                rw [eval_value] at hw
                exact ihE _ _ _ _ _ _ hgo ρs' ρo' w ha' hs' hw
          refine ⟨fun ρs ρo v ha hs hv => ?_, fun ref outs hout => ⟨sp', name, rfl, ?_⟩⟩
          · rw [hcode, out_call_toOption, bind_toOption] at hv
            rw [eval_call_toOption, hcall ρs ρo _ ha hs hv]
            rfl
          · rw [hcode] at hout
            injection hout with h1 h2
            subst h1 h2
            exact hcall
        · simp at h
  case member sp' obj test =>
    cases obj
    case ident sp'' oname =>
      by_cases hn : oname = "Number"
      · subst hn
        simp at h
        cases hN : env.has "Number" <;> simp [hN] at h
        cases hT : numberTest? test <;> simp [hT] at h
        rename_i form
        match args, h with
        | [arg], h =>
          simp at h
          obtain ⟨a, s₁, hta, h⟩ := h
          split at h
          · simp at h
            obtain ⟨hcode, -⟩ := h
            refine ⟨fun ρs ρo v ha hs hv => ?_, fun ref outs hout => by rw [← hcode] at hout; cases hout⟩
            rw [← hcode] at hv
            obtain ⟨n, hn, rfl⟩ := out_numberTest fs fuel hv
            rw [eval_value] at hn
            have harg := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hn
            have hnone := hs.none hN
            unfold numberTest? at hT
            split at hT <;> cases hT <;>
              simp [Eval.eval, hnone, harg, IR.NumberTest.apply]
          · simp at h
        | [], h => simp at h
        | _ :: _ :: _, h => simp at h
      · by_cases hM : oname = "Math"
        · subst hM
          simp [hn] at h
          cases hMa : env.has "Math" <;> simp [hMa] at h
          obtain ⟨hsim, op, outs, hcode⟩ :=
            translateMathCall_sound m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h) hMa h
          exact ⟨hsim, fun ref outs' hout => by rw [hcode] at hout; cases hout⟩
        · by_cases hO : oname = "Object"
          · subst hO
            by_cases hi : test = "is"
            · subst hi
              simp at h
              cases hOb : env.has "Object" <;> simp [hOb] at h
              obtain ⟨hsim, hnc⟩ :=
                translateObjectIs_sound m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h) hOb h
              exact ⟨hsim, fun ref outs' hout => absurd hout (hnc ref outs')⟩
            · simp [hi] at h
              cases hOb : env.has "Object" <;> simp [hOb] at h
              obtain ⟨hsim, hnc⟩ :=
                translateDictionaryCall_sound m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h) hOb h
              exact ⟨hsim, fun ref outs' hout => absurd hout (hnc ref outs')⟩
          · by_cases hDt : oname = "Date"
            · subst hDt
              by_cases hu : test = "UTC"
              · subst hu
                simp at h
                cases hDb : env.has "Date" <;> simp [hDb] at h
                obtain ⟨hsim, hnc⟩ :=
                  translateDateUtc_sound m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h) hDb h
                exact ⟨hsim, fun ref outs' hout => absurd hout (hnc ref outs')⟩
              · by_cases hp : test = "parse"
                · subst hp
                  simp at h
                  cases hDb : env.has "Date" <;> simp [hDb] at h
                  obtain ⟨hsim, hnc⟩ := translateDateParse_sound (N := N) m fs fuel hDb h
                  exact ⟨hsim, fun ref outs' hout => absurd hout (hnc ref outs')⟩
                · simp [hu, hp] at h
            · by_cases hj : oname = "JSON"
              · -- `JSON.stringify(x)`: the value that `jsonStringify` gives.
                subst hj
                simp at h
                cases hN : env.has "JSON" <;> simp [hN] at h
                by_cases ht : test = "stringify"
                · subst ht
                  simp only [if_true] at h
                  match args, h with
                  | [arg], h =>
                    simp only [bind_ok] at h
                    obtain ⟨a, s₁, hta, h⟩ := h
                    have hcode := jsonCall_code h
                    refine ⟨fun ρs ρo v ha hs hv => ?_, fun ref outs hout => by rw [hcode] at hout; cases hout⟩
                    rw [hcode] at hv
                    simp only [IR.Expr.eval, IR.Expr.evalList] at hv
                    cases hx : IR.Expr.eval fs fuel ρo a.value with
                    | none => simp [hx] at hv
                    | some w =>
                      simp [hx, IR.ExprExt.apply] at hv
                      rw [eval_value] at hx
                      have harg := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hx
                      have hnone := hs.none hN
                      simp [Eval.eval, hnone, harg, hv]
                  | [], h => simp at h
                  | _ :: _ :: _, h => simp at h
                · simp [ht] at h
              · simp [hn, hM, hO, hDt, hj] at h
    all_goals simp at h

/-- An object literal of an interface, or of a member of a tagged union. -/
theorem translateObject_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    (ihO : ∀ env exp s ps ctx c ctx', translateObject F env exp s ps ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.object s ps) c.code)
    {env : Translate.Env} {exp : Option Ty} {sp : Span} {props : List Property} {ctx ctx' : Ctx}
    {c : Code} (h : translateObject (F + 1) env exp sp props ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.object sp props) c.code := by
  simp only [translateObject] at h
  simp at h
  obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
  cases exp with
  | none => simp at h
  | some t =>
    cases t
    case tagged uref tags =>
      -- A member of a tagged union: the structure of the member, which the
      -- evaluator gives as it is.
      simp only [bind_ok, orReject_ok, ite_state] at h
      obtain ⟨union, _, ⟨-, rfl⟩, field, _, ⟨-, rfl⟩, tag, _, ⟨-, rfl⟩, h⟩ := h
      split at h
      · simp only [bind_ok, orReject_ok] at h
        obtain ⟨member, _, ⟨-, rfl⟩, h⟩ := h
        simp only [map_ok] at h
        obtain ⟨inner, hinner, rfl⟩ := h
        intro ρs ρo v ha hs hv
        simp only [IR.Expr.eval] at hv
        exact ihO _ _ _ _ _ _ _ hinner ρs ρo v ha hs hv
      · simp at h
    all_goals try simp at h
    rename_i structName structArgs
    obtain ⟨info, _, ⟨-, rfl⟩, seen, parts, s₂, hfold, h⟩ := h
    have hparts : c.code = .struct parts structName (Ty.leanList structArgs) := by
      obtain ⟨_, _, -, h⟩ := h
      split at h
      · simp at h; rw [← h.1]
      · simp at h
    have key := fold_sim (N := N) (env := env) m fs fuel ?hstep props [] [] _ _ _ hfold
    · obtain ⟨new, hnew, hsim⟩ := key
      intro ρs ρo v ha hs hv
      rw [hparts] at hv
      simp only at hnew
      rw [hnew] at hv
      simp only [IR.Expr.eval, List.nil_append] at hv
      cases hx : IR.Expr.evalFields fs fuel ρo new with
      | none => simp [hx] at hv
      | some fvs =>
        simp [hx] at hv
        subst hv
        -- The properties have values, so the first is not a spread, which
        -- `evalProps` does not read.
        have hev := hsim ρs ρo fvs ha hs hx
        rcases props with _ | ⟨p, ps⟩
        · simp [Eval.eval, hev]
        · cases p with
          | spread _ _ => simp [Eval.evalProps] at hev
          | _ => simp [Eval.eval, hev]
    case hstep =>
      intro a acc p c₀ r c₁ hg
      cases p with
      | shorthand ps name =>
        simp at hg
        obtain ⟨fieldType, _, ⟨-, rfl⟩, hg⟩ := hg
        split at hg
        · simp at hg
        · simp at hg
          obtain ⟨v, _, hv, hg⟩ := hg
          split at hg
          · simp at hg
            obtain ⟨rfl, -⟩ := hg
            refine ⟨name, _, rfl, ?_⟩
            intro ρs ρo w ha hs hw rest
            rw [fieldValue_into_eval] at hw
            rw [eval_value] at hw
            have := ihE _ _ _ _ _ _ hv ρs ρo w ha hs hw
            simp [Eval.evalProps, this]
            cases Eval.evalProps m fuel ρs rest <;> rfl
          · simp only [map_ok, reject_ne_ok, false_and, exists_false] at hg
      | spread ps v => simp at hg
      | keyValue ps key val =>
        cases key with
        | ident key =>
          by_cases hk : key = "__proto__"
          · subst hk; simp at hg
          simp [hk] at hg
          obtain ⟨fieldType, _, ⟨-, rfl⟩, hg⟩ := hg
          split at hg
          · simp at hg
          · simp at hg
            obtain ⟨v, _, hv, hg⟩ := hg
            split at hg
            · simp at hg
              obtain ⟨rfl, -⟩ := hg
              refine ⟨key, _, rfl, ?_⟩
              intro ρs ρo w ha hs hw rest
              rw [fieldValue_into_eval] at hw
              rw [eval_value] at hw
              have := ihE _ _ _ _ _ _ hv ρs ρo w ha hs hw
              simp [Eval.evalProps, this, hk]
              cases Eval.evalProps m fuel ρs rest <;> rfl
            · simp only [map_ok, reject_ne_ok, false_and, exists_false] at hg
        | _ => simp at hg

/-- What a read of a `Record` gives: the property of an object that a string
names. It splits each value on its own, so a new kind of value adds one case,
not one for each other kind. -/
theorem apply_recordGet {r : DeclRef} {keys : List String} {ov kv v : Val N}
    (h : IR.ExprExt.apply (.recordGet r keys) [ov, kv] = some v) :
    ∃ fields k, ov = .obj fields ∧ kv = .str k ∧ Eval.getKey fields k = some v := by
  cases ov <;> simp [IR.ExprExt.apply] at h
  cases kv <;> simp at h
  exact ⟨_, _, rfl, rfl, h⟩

theorem apply_recordGetFlatten {r : DeclRef} {keys : List String} {ov kv v : Val N}
    (h : IR.ExprExt.apply (.recordGetFlatten r keys) [ov, kv] = some v) :
    ∃ fields k, ov = .obj fields ∧ kv = .str k ∧ Eval.getKey fields k = some v := by
  cases ov <;> simp [IR.ExprExt.apply] at h
  cases kv <;> simp at h
  exact ⟨_, _, rfl, rfl, h⟩

theorem regexpLiteral_sound {F : Nat} {env : Translate.Env} {expected : Option Ty}
    {sp : Span} {source : String} {target : Edition} {ctx ctx' : Ctx} {c : Code}
    (h : translateExprCore (F + 1) env expected (.regexp sp source target) ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.regexp sp source target) c.code := by
  simp [translateExprCore] at h
  obtain ⟨s₁, ⟨-, rfl⟩, r, ⟨hparse, rfl⟩, rfl⟩ := h
  intro ρs ρo v _ _ hv
  simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] at hv
  subst v
  simp [Eval.eval, hparse]

set_option maxHeartbeats 800000 in
theorem expr_sound (hc : CallsAgree (N := N) m.program fs fuel) (F : Nat) :
    (∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code) ∧
    (∀ env exp s es ctx r ctx', translateElements F env exp s es ctx = .ok r ctx' →
      SimList (N := N) m fs fuel env es r.1) ∧
    (∀ env exp s es ctx c ctx', translateArray F env exp s es ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.array s es) c.code) ∧
    (∀ env s callee args top ctx c ctx', translateCall F env s callee args top ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.call s callee args) c.code ∧
        CallSim (N := N) m fs fuel env callee args c.code) ∧
    (∀ env exp s ps ctx c ctx', translateObject F env exp s ps ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.object s ps) c.code) ∧
    (∀ env s op l r ctx c ctx', translateBinary F env s op l r ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.binary s op l r) c.code) ∧
    (∀ env exp s recv method args ctx c ctx', translateArrayMethod F env exp s recv method args ctx = .ok c ctx' →
      ∀ sp name, listMethod? name = some method →
        Sim (N := N) m fs fuel env (.call s (.member sp recv name) args) c.code) ∧
    (∀ env exp s recv args ctx c ctx', translateReduce F env exp s recv args ctx = .ok c ctx' →
      ∀ sp, Sim (N := N) m fs fuel env (.call s (.member sp recv "reduce") args) c.code) ∧
    (∀ env s recv method args ctx c ctx', translateSort F env s recv method args ctx = .ok c ctx' →
      method = "toSorted" ∨ method = "sort" →
      ∀ sp, Sim (N := N) m fs fuel env (.call s (.member sp recv method) args) c.code) ∧
    (∀ env s recv op args ctx c ctx', translateMapMethod F env s recv op args ctx = .ok c ctx' →
      ∀ sp name, mapMethodOf (.member sp recv name) = some (recv, op) →
        Sim (N := N) m fs fuel env (.call s (.member sp recv name) args) c.code) ∧
    (∀ env s recv method args ctx c ctx', translateArrayCall F env s recv method args ctx = .ok c ctx' →
      ∀ sp, recv.namesGlobal = false →
        Sim (N := N) m fs fuel env (.call s (.member sp recv method) args) c.code) ∧
    (∀ env s o elem key ctx c ctx', translateArrayIndex F env s o elem key ctx = .ok c ctx' →
      ∀ sp obj, Sim (N := N) m fs fuel env obj o.value →
        Sim (N := N) m fs fuel env (.index sp obj key) c.code) ∧
    (∀ env s base rest ctx c ctx', translateSpread F env s base rest ctx = .ok c ctx' →
      ∀ sp, Sim (N := N) m fs fuel env (.object s (.spread sp base :: rest)) c.code) ∧
    (∀ env exp e ctx c ctx', translateExprCore F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code) := by
  induction F with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [translateExpr, translateElements, translateArray, translateCall, translateObject,
        translateBinary, translateArrayMethod, translateReduce, translateSort, translateMapMethod, translateArrayCall, translateArrayIndex, translateSpread,
        translateExprCore]
  | succ F ih =>
    obtain ⟨ihE, ihL, ihA, ihC, ihO, ihB, ihM, ihR, ihT, ihMM, ihK, ihI, ihS, ihX⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- The core first, then the step that makes a value a member of a union.
    rotate_right
    · intro env exp e ctx c ctx' h
      cases e with
      | paren sp inner =>
        simp only [translateExprCore] at h
        intro ρs ρo v ha hs hv
        rw [Eval.eval]
        exact ihX _ _ _ _ _ _ h ρs ρo v ha hs hv
      | asConst sp inner =>
        simp only [translateExprCore] at h
        intro ρs ρo v ha hs hv
        rw [Eval.eval]
        exact ihX _ _ _ _ _ _ h ρs ρo v ha hs hv
      | satisfies sp inner type =>
        simp only [translateExprCore, bind_ok] at h
        obtain ⟨t, s₁, -, c', s₂, hc', h⟩ := h
        simp only [ite_state] at h
        split at h
        · obtain ⟨rfl, -⟩ := h
          intro ρs ρo v ha hs hv
          rw [Eval.eval]
          rcases firstFitting_ok hc' with hx | hy
          · exact ihX _ _ _ _ _ _ hx ρs ρo v ha hs hv
          · exact ihX _ _ _ _ _ _ hy ρs ρo v ha hs hv
        · simp at h
      | bigint sp text =>
        simp only [translateExprCore] at h
        simp at h
        obtain ⟨n, ⟨hv, -⟩, rfl⟩ := h
        intro ρs ρo v _ _ hv'
        simp [IR.Expr.eval] at hv'
        subst hv'
        simp [Eval.eval]; simpa [bigintValue?] using hv
      | number sp text =>
        simp only [translateExprCore] at h
        simp at h
        obtain ⟨n, ⟨hv, -⟩, rfl⟩ := h
        intro ρs ρo v _ _ hv'
        simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] at hv'
        subst hv'
        simp [Eval.eval]; exact ⟨n, by simpa [safeIntegerValue?] using hv, rfl⟩
      | null sp =>
        simp [translateExprCore] at h
        obtain ⟨rfl, -⟩ := h
        intro ρs ρo v _ _ hv'
        simp [IR.Expr.eval] at hv'
        subst hv'; simp [Eval.eval]
      | bool sp b =>
        simp [translateExprCore] at h
        obtain ⟨rfl, -⟩ := h
        intro ρs ρo v _ _ hv'
        simp [IR.Expr.eval] at hv'
        subst hv'; simp [Eval.eval]
      | regexp sp source target =>
        exact regexpLiteral_sound m fs fuel h
      | string sp str =>
        -- A string, or the constructor of a literal union for it: either is
        -- the string.
        have hcode : ∀ ρ : Eval.Env N, IR.Expr.eval fs fuel ρ c.code = some (.str str) := by
          intro ρ
          simp only [translateExprCore] at h
          split at h
          all_goals simp only [bind_ok, get_ok, orReject_ok, ite_state, pure_ok] at h
          all_goals first
            | (obtain ⟨rfl, -⟩ := h; simp [IR.Expr.eval])
            | (obtain ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨-, rfl⟩, h⟩ := h
               split at h
               · simp at h
               simp only [pure_bind] at h
               split at h
               · simp at h
                 obtain ⟨rfl, -⟩ := h
                 simp [IR.Expr.eval]
               · simp at h)
            | (split at h
               · obtain ⟨rfl, -⟩ := h
                 simp [IR.Expr.eval]
               · simp at h)
        intro ρs ρo v _ _ hv'
        rw [hcode] at hv'
        simp at hv'
        subst hv'; simp [Eval.eval]
      | ident sp name =>
        simp only [translateExprCore] at h
        intro ρs ρo v ha hs hv'
        cases hl : env.lookup name with
        | none =>
          simp only [hl] at h
          have hnone : ρs.lookup name = none := hs.none (by simp [Translate.Env.has, hl])
          split at h
          · -- `undefined`, where an optional value is expected.
            rename_i hu
            have hu' : name = "undefined" := by simpa using hu
            subst hu'
            split at h
            · simp only [pure_ok] at h
              obtain ⟨rfl, -⟩ := h
              simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] at hv'
              subst hv'
              simp [Eval.eval, hnone]
            · simp at h
          cases hk : numberConstant? name with
          | none => simp [hk] at h
          | some k =>
            simp [hk] at h
            obtain ⟨rfl, -⟩ := h
            simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] at hv'
            subst hv'
            unfold numberConstant? at hk
            split at hk
            · cases hk; simp only [Eval.eval, hnone]; simp [IR.NumberConstant.value]
            · cases hk; simp only [Eval.eval, hnone]; simp [IR.NumberConstant.value]
            · cases hk
        | some l =>
          simp only [hl] at h
          -- A local function may only be called.
          split at h
          · simp at h
          simp at h
          obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
          have hc : c.code = .var name := by
            split at h
            · simp at h
            · simp at h
              obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
              split at h
              · simp at h
              · simp at h; rw [← h.1]
          rw [hc] at hv'
          simp only [IR.Expr.eval] at hv'
          rw [← ha name] at hv'
          simp only [Eval.eval, hv']
      | member sp obj name => exact translateMember_sound m fs fuel ihE h
      | optMember sp obj name =>
        simp only [translateExprCore, bind_ok] at h
        obtain ⟨o, s₁, ho, ⟨bind, ty⟩, s₂, -, h⟩ := h
        simp only [pure_ok] at h
        obtain ⟨rfl, -⟩ := h
        intro ρs ρo v ha hs hv'
        simp only [IR.Expr.eval, IR.Expr.evalList] at hv'
        rw [nullableConditionalReceiver_eval] at hv'
        cases hobj : IR.Expr.eval fs fuel ρo o.code with
        | none => simp [hobj] at hv'
        | some ov =>
          have := ihE _ _ _ _ _ _ ho ρs ρo ov ha hs hobj
          simp only [hobj] at hv'
          simp only [Eval.eval, this, Option.bind_eq_bind, Option.bind_some]
          cases ov <;> simp only [IR.ExprExt.apply] at hv' <;> first | exact hv' | simp at hv'
      | optIndex sp obj key =>
        simp only [translateExprCore, bind_ok] at h
        obtain ⟨o, s₁, ho, h⟩ := h
        generalize htu : o.type.maybeValue?.bind Ty.tupleElems? = tuple at h
        cases tuple
        case some tys =>
          dsimp only at h
          split at h
          · rename_i sp' text
            simp only [bind_ok, orReject_ok, ite_state] at h
            obtain ⟨k, s₂, ⟨hk, rfl⟩, elem, s₃, ⟨_, rfl⟩, h⟩ := h
            split at h
            · rename_i hpos
              simp only [pure_bind, ite_state] at h
              split at h
              · simp at h
              simp only [pure_ok] at h
              obtain ⟨rfl, _⟩ := h
              intro ρs ρo v ha hs hv
              simp only [IR.Expr.eval, IR.Expr.evalList] at hv
              rw [nullableConditionalReceiver_eval] at hv
              cases hx : IR.Expr.eval fs fuel ρo o.value with
              | none => simp [hx] at hv
              | some w =>
                have hobj := ihE _ _ _ _ _ _ ho ρs ρo w ha hs
                  (by rw [← eval_value]; exact hx)
                rw [Eval.eval.eq_def]
                simp only [hobj, Option.bind_eq_bind, Option.bind_some]
                cases w
                case list items =>
                  change Eval.numberLiteral text = some k at hk
                  simp only [hx, Option.bind_eq_bind, Option.bind_some, pure_bind,
                    IR.ExprExt.apply, IR.optionalLiteralIndex, Option.some.injEq, Int.toNat_of_nonneg hpos] at hv
                  simp [Eval.optionalIndexValue, Eval.numberText?, hk, hv]
                case null => simpa [hx, IR.ExprExt.apply] using hv
                case undefined => simpa [hx, IR.ExprExt.apply] using hv
                all_goals simp [hx, IR.ExprExt.apply] at hv
            · simp at h
          · simp at h
        simp only [bind_ok, get_ok] at h
        obtain ⟨ctx, s₂, ⟨rfl, rfl⟩, h⟩ := h
        generalize hr : o.type.maybeValue?.bind (recordIndex s₂) = record at h
        cases record
        case some r =>
          rcases r with ⟨keyRef, keys, type⟩
          dsimp only at h
          simp only [ite_state] at h
          split at h
          · simp at h
          simp only [pure_bind, bind_ok, ite_state] at h
          obtain ⟨k, s₂, hk, h⟩ := h
          split at h
          · simp only [pure_ok] at h
            obtain ⟨rfl, _⟩ := h
            intro ρs ρo v ha hs hv
            simp only [IR.Expr.eval, IR.Expr.evalList] at hv
            rw [nullableConditionalReceiver_eval] at hv
            cases hx : IR.Expr.eval fs fuel ρo o.value with
            | none => simp [hx] at hv
            | some w =>
              cases hy : IR.Expr.eval fs fuel ρo k.value with
              | none => simp [hx, hy] at hv
              | some j =>
                have hobj := ihE _ _ _ _ _ _ ho ρs ρo w ha hs
                  (by rw [← eval_value]; exact hx)
                have hkey := ihE _ _ _ _ _ _ hk ρs ρo j ha hs
                  (by rw [← eval_value]; exact hy)
                rw [Eval.eval.eq_def]
                simp only [hobj, Option.bind_eq_bind, Option.bind_some]
                cases w
                case null =>
                  split at hv <;> simp [hx, hy, IR.ExprExt.apply] at hv
                  all_goals change some Val.undefined = some v
                  all_goals exact congrArg some hv
                case undefined =>
                  split at hv <;> simp [hx, hy, IR.ExprExt.apply] at hv
                  all_goals change some Val.undefined = some v
                  all_goals exact congrArg some hv
                case obj fields =>
                  cases j <;> split at hv <;> simp [hx, hy, IR.ExprExt.apply] at hv
                  all_goals first
                    | (change ((Eval.optionalIndexValue (.obj fields) key
                        (fun _ => Eval.eval m fuel ρs key)) = some v)
                      ; simpa [Eval.optionalIndexValue, hkey] using hv)
                    | simp [Eval.eval, Eval.optionalIndexValue, hkey, hv]
                all_goals split at hv <;> simp [hx, hy, IR.ExprExt.apply] at hv
          · simp at h
        simp only [bind_ok, orReject_ok] at h
        obtain ⟨elem, s₂, ⟨_, rfl⟩, h⟩ := h
        simp only [ite_state] at h
        split at h
        · simp at h
        simp only [pure_bind] at h
        split at h
        · rename_i sp' text
          simp only [bind_ok, orReject_ok, ite_state] at h
          obtain ⟨k, s₃, ⟨hk, rfl⟩, h⟩ := h
          split at h
          · rename_i hpos
            simp only [pure_ok] at h
            obtain ⟨rfl, _⟩ := h
            intro ρs ρo v ha hs hv
            simp only [IR.Expr.eval, IR.Expr.evalList] at hv
            rw [nullableConditionalReceiver_eval] at hv
            cases hx : IR.Expr.eval fs fuel ρo o.value with
            | none => simp [hx] at hv
            | some w =>
              have hobj := ihE _ _ _ _ _ _ ho ρs ρo w ha hs
                (by rw [← eval_value]; exact hx)
              rw [Eval.eval.eq_def]
              simp only [hobj, Option.bind_eq_bind, Option.bind_some]
              cases w
              case list items =>
                change Eval.numberLiteral text = some k at hk
                simp only [hx, Option.bind_eq_bind, Option.bind_some, pure_bind,
                  IR.ExprExt.apply, IR.optionalLiteralIndex, Option.some.injEq, Int.toNat_of_nonneg hpos] at hv
                simp [Eval.optionalIndexValue, Eval.numberText?, hk, hv]
              case null => simpa [hx, IR.ExprExt.apply] using hv
              case undefined => simpa [hx, IR.ExprExt.apply] using hv
              all_goals simp [hx, IR.ExprExt.apply] at hv
          · simp at h
        · rename_i hnot
          have hnt : Eval.numberText? key = none := by
            cases key <;> simp [Eval.numberText?] at hnot ⊢
          simp only [bind_ok] at h
          obtain ⟨i, s₂, hi, h⟩ := h
          simp only [ite_state] at h
          split at h
          · simp only [pure_ok] at h
            obtain ⟨rfl, _⟩ := h
            intro ρs ρo v ha hs hv
            simp only [IR.Expr.eval, IR.Expr.evalList] at hv
            rw [nullableConditionalReceiver_eval] at hv
            cases hx : IR.Expr.eval fs fuel ρo o.value with
            | none => simp [hx] at hv
            | some w =>
              cases hy : IR.Expr.eval fs fuel ρo i.value with
              | none => simp [hx, hy] at hv
              | some j =>
                have hobj := ihE _ _ _ _ _ _ ho ρs ρo w ha hs
                  (by rw [← eval_value]; exact hx)
                have hkey := ihE _ _ _ _ _ _ hi ρs ρo j ha hs
                  (by rw [← eval_value]; exact hy)
                rw [Eval.eval.eq_def]
                simp only [hobj, Option.bind_eq_bind, Option.bind_some]
                cases w
                case null => simpa [hx, hy, IR.ExprExt.apply] using hv
                case undefined => simpa [hx, hy, IR.ExprExt.apply] using hv
                case list items =>
                  cases j <;> simp [hx, hy, IR.ExprExt.apply] at hv
                  simp [Eval.optionalIndexValue, hnt, hkey, hv]
                all_goals simp [hx, hy, IR.ExprExt.apply] at hv
          · simp at h
      | index sp obj key =>
        simp only [translateExprCore, bind_ok] at h
        obtain ⟨o, s₁, ho, h⟩ := h
        cases hot : o.type.tupleElems? with
        | some tys =>
          -- `t[i]`: the element `i` of the tuple, which the array has at `i`.
          simp only [hot] at h
          cases key
          case number sp' text =>
            simp only [bind_ok, orReject_ok] at h
            obtain ⟨i, s₂, ⟨hi, rfl⟩, h⟩ := h
            cases hti : tys[i.toNat]? with
            | none => simp [hti] at h
            | some ty =>
              simp only [hti] at h
              split at h
              · next hpos =>
                simp at h
                obtain ⟨rfl, -⟩ := h
                intro ρs ρo v ha hs hv
                simp only [IR.Expr.eval] at hv
                cases hx : IR.Expr.eval fs fuel ρo o.code with
                | none => simp [hx] at hv
                | some w =>
                  cases w
                  case list items =>
                    simp [hx] at hv
                    have hobj := ihE _ _ _ _ _ _ ho ρs ρo _ ha hs hx
                    have hlit : Eval.numberLiteral text = some i := hi
                    simp only [Eval.eval, hobj, Eval.numberText?, hlit, Option.bind_eq_bind, Option.bind_some,
                      Eval.elementAt] at hpos ⊢
                    simp [hpos, hv]
                  all_goals simp [hx] at hv
              · simp at h
          all_goals simp at h
        | none =>
        simp only [hot] at h
        cases hel : o.type.element? with
        | some elem =>
          -- `xs[i]` on an array: the element at the index, as the spec reads it.
          simp only [hel] at h
          exact ihI _ _ _ _ _ _ _ _ h sp obj fun ρs ρo w ha hs hw =>
            ihE _ _ _ _ _ _ ho ρs ρo w ha hs (by rwa [eval_value] at hw)
        | none =>
        -- `r[k]` on a `Record<K, V>`: the evaluator reads the property that
        -- the string names, as the spec does.
        simp only [hel] at h
        simp at h
        obtain ⟨_, _, ⟨rfl, rfl⟩, keyRef, keys, ty, _, ⟨-, rfl⟩, k, s₃, hk, h⟩ := h
        generalize (if keyRef.file = IR.dictionaryRef.file ∧ keyRef.name = IR.dictionaryRef.name
          then Ty.string else .enum keyRef) = keyType at hk h
        split at h
        · simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          intro ρs ρo v ha hs hv'
          simp only [IR.Expr.eval, IR.Expr.evalList, eval_value] at hv'
          cases hobj : IR.Expr.eval fs fuel ρo o.code with
          | none => simp [hobj] at hv'
          | some ov =>
            cases hkey : IR.Expr.eval fs fuel ρo k.code with
            | none => simp [hobj, hkey] at hv'
            | some kv =>
              have h1 := ihE _ _ _ _ _ _ ho ρs ρo ov ha hs hobj
              have h2 := ihE _ _ _ _ _ _ hk ρs ρo kv ha hs hkey
              simp only [hobj, hkey, Option.bind_eq_bind, Option.bind_some, pure_bind] at hv'
              simp only [Eval.eval, h1, h2, Option.bind_eq_bind, Option.bind_some]
              have hrecord : ∃ fields k, ov = .obj fields ∧ kv = .str k ∧
                  Eval.getKey fields k = some v := by
                cases ty with
                | optional inner =>
                  cases inner with
                  | optional value =>
                    simp at hv'
                    exact apply_recordGetFlatten hv'
                  | _ =>
                    simp at hv'
                    exact apply_recordGet hv'
                | _ =>
                  simp at hv'
                  exact apply_recordGet hv'
              obtain ⟨fields, k, rfl, rfl, hget⟩ := hrecord
              simp_all
        · simp at h
      | unary sp op arg =>
        simp only [translateExprCore] at h
        intro ρs ρo v ha hs hv'
        cases op with
        | not =>
          simp +decide at h
          obtain ⟨a, s₁, hta, h⟩ := h
          split at h
          · simp at h
            obtain ⟨hcode, -⟩ := h
            rw [← hcode] at hv'
            have key : ∃ b, IR.Expr.eval fs fuel ρo a.code = some (.bool b) ∧ v = .bool !b := by
              by_cases hp : a.prop = true
              · simp only [hp, if_true] at hv'; exact out_propNot fs fuel hv'
              · simp only [hp] at hv'; exact out_not fs fuel hv'
            obtain ⟨b, hb, rfl⟩ := key
            have := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hb
            simp [Eval.eval, this, Val.truthy]
          · simp at h
        | neg =>
          simp +decide at h
          split at h
          · next hcond =>
            simp at h
            obtain ⟨hcode, -⟩ := h
            rw [← hcode] at hv'
            simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply, IR.NumberConstant.value] at hv'
            subst hv'
            obtain ⟨hm, hhas⟩ := hcond
            have hnone := hs.none hhas
            obtain ⟨s', rfl⟩ := isInfinity_eq_true hm
            simp only [Eval.eval, hnone]
          · next hcond =>
            simp at h
            obtain ⟨a, s₁, hta, h⟩ := h
            have hInf : ∀ s', arg = .ident s' "Infinity" → (ρs.lookup "Infinity").isSome := by
              rintro s' rfl
              apply hs.some
              simpa [Expr.isInfinity] using hcond
            cases ht : a.type <;> simp [ht] at h
            · obtain ⟨hcode, -⟩ := h
              rw [← hcode] at hv'
              obtain ⟨i, hi, rfl⟩ := out_neg fs fuel hv'
              rw [eval_value] at hi
              have := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hi
              rw [eval_neg m fuel sp arg ρs _ this hInf]; rfl
            · obtain ⟨hcode, -⟩ := h
              rw [← hcode] at hv'
              obtain ⟨n, hn, rfl⟩ := out_numberNeg fs fuel hv'
              rw [eval_value] at hn
              have := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hn
              rw [eval_neg m fuel sp arg ρs _ this hInf]; rfl
        | bitNot =>
          simp +decide at h
          obtain ⟨a, s₁, hta, h⟩ := h
          split at h
          · simp at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨n, hn, rfl⟩ := out_numberFn fs fuel hv'
            rw [eval_value] at hn
            have := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hn
            simp [Eval.eval, this, IR.NumberFn.apply]
          split at h
          · simp at h
            obtain ⟨⟨-, -⟩, rfl⟩ := h
            obtain ⟨i, hi, rfl⟩ := out_bigintNot fs fuel hv'
            rw [eval_value] at hi
            have := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hi
            simp [Eval.eval, this]
          · simp at h
        | _ => simp +decide at h
      | binary sp op l r =>
        simp only [translateExprCore] at h
        exact ihB _ _ _ _ _ _ _ _ h
      | call sp callee args =>
        simp only [translateExprCore] at h
        cases hred : reduceOf callee with
        | some recv =>
          simp only [hred] at h
          unfold reduceOf at hred
          split at hred
          · rename_i sp' recv'
            cases hred
            exact ihR _ _ _ _ _ _ _ _ h sp'
          · simp at hred
        | none =>
        simp only [hred] at h
        cases hso : sortOf callee with
        | some rm =>
          obtain ⟨recv, method⟩ := rm
          simp only [hso] at h
          obtain ⟨sp', rfl, hmethod⟩ := sortOf_some hso
          exact ihT _ _ _ _ _ _ _ _ h hmethod sp'
        | none =>
        simp only [hso] at h
        cases hm : arrayMethodOf callee with
        | some rm =>
          obtain ⟨recv, method⟩ := rm
          simp only [hm] at h
          unfold arrayMethodOf at hm
          split at hm
          · rename_i sp' recv' name
            cases hl : listMethod? name with
            | none => simp [hl] at hm
            | some lm =>
              simp [hl] at hm
              obtain ⟨rfl, rfl⟩ := hm
              exact ihM _ _ _ _ _ _ _ _ _ h sp' name hl
          · simp at hm
        | none =>
          simp only [hm] at h
          cases hmm : mapMethodOf callee with
          | some ro =>
            obtain ⟨recv, op⟩ := ro
            simp only [hmm] at h
            obtain ⟨sp', name, rfl⟩ : ∃ sp' name, callee = .member sp' recv name := by
              cases callee <;> simp [mapMethodOf] at hmm
              rename_i sp' o name
              obtain ⟨rfl, -⟩ := (mapMethodOf_some hmm)
              exact ⟨_, _, rfl⟩
            exact ihMM _ _ _ _ _ _ _ _ h sp' name hmm
          | none =>
            simp only [hmm] at h
            cases hk : arrayCallOf callee with
            | some rk =>
              obtain ⟨recv, method⟩ := rk
              simp only [hk] at h
              unfold arrayCallOf at hk
              split at hk
              · rename_i sp' recv' name
                split at hk
                · simp at hk
                · rename_i hn
                  simp only [Option.some.injEq, Prod.mk.injEq] at hk
                  obtain ⟨rfl, rfl⟩ := hk
                  exact ihK _ _ _ _ _ _ _ _ h sp' (by simpa using hn)
              · simp at hk
            | none =>
              simp only [hk] at h
              exact (ihC _ _ _ _ _ _ _ _ h).1
      | object sp props =>
        simp only [translateExprCore] at h
        cases hsp : spreadOf props with
        | some br =>
          obtain ⟨base, rest⟩ := br
          simp only [hsp] at h
          obtain ⟨sp', rfl⟩ := spreadOf_some hsp
          exact ihS _ _ _ _ _ _ _ h sp'
        | none =>
          simp only [hsp] at h
          exact ihO _ _ _ _ _ _ _ h
      | array sp elems =>
        simp only [translateExprCore] at h
        cases hexp : exp with
        | none => rw [hexp] at h; exact ihA _ _ _ _ _ _ _ h
        | some t =>
          rw [hexp] at h
          cases t
          case tuple tys =>
            -- A tuple: the list of its elements, as the array literal is.
            simp only at h
            split at h
            · next hlen =>
              simp only [bind_ok, pure_ok] at h
              obtain ⟨_, _, ⟨-, rfl⟩, codes, s₁, hcodes, hcode, -⟩ := h
              intro ρs ρo v ha hs hv
              rw [← hcode] at hv
              simp only [IR.Expr.eval] at hv
              cases hx : IR.Expr.evalList fs fuel ρo (codes.map Code.value) with
              | none => simp [hx] at hv
              | some vs =>
                simp [hx] at hv
                subst hv
                have hel := zip_sim_value m fs fuel ?hg elems tys _ codes _ (Nat.le_of_eq (by simpa using hlen)) hcodes
                  ρs ρo vs ha hs hx
                · simp [Eval.eval, evalElems_of_evalList m fuel hel]
                case hg =>
                  intro x t c₀ o c₁ hgo
                  simp only [bind_ok] at hgo
                  obtain ⟨a, s₂, hta, hgo⟩ := hgo
                  split at hgo
                  · simp at hgo
                    obtain ⟨rfl, -⟩ := hgo
                    intro ρs' ρo' w ha' hs' hw
                    rw [eval_value] at hw
                    exact ihE _ _ _ _ _ _ hta ρs' ρo' w ha' hs' hw
                  · simp at hgo
            · simp at h
          all_goals exact ihA _ _ _ _ _ _ _ h
      | cond sp test ifTrue ifFalse =>
        simp only [translateExprCore] at h
        rcases narrowFallback_ok h with h | h
        · simp at h
          obtain ⟨tc, s₁, htc, h⟩ := h
          split at h
          · simp at h
            obtain ⟨ta, s₂, hta, tb, s₃, htb, h⟩ := h
            obtain ⟨ty, ⟨-, -⟩, hcode⟩ := h
            intro ρs ρo v ha hs hv'
            rw [← hcode] at hv'
            have hv' : IR.Expr.eval fs fuel ρo
                (.ite tc.code (ta.into env.unions (some ty)).value
                  (tb.into env.unions (some ty)).value) = some v := by
              split at hv' <;> simpa only [IR.Expr.eval] using hv'
            obtain ⟨t, ht, hbr⟩ := out_ite fs fuel hv'
            have htest := ihE _ _ _ _ _ _ htc ρs ρo _ ha hs ht
            simp only [Eval.eval, htest, Option.bind_eq_bind, Option.bind_some, Val.truthy]
            cases t
            · simp only [eval_value, eval_into] at hbr ⊢
              exact ihE _ _ _ _ _ _ htb ρs ρo _ ha hs hbr
            · simp only [if_true, eval_value, eval_into] at hbr ⊢
              exact ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hbr
          · simp at h
        · cases hn : optionTestOf env test with
          | none => simp [hn] at h
          | some t =>
            obtain ⟨name, isEq, value, kind⟩ := t
            simp [hn] at h
            obtain ⟨ta, s₁, hta, tb, s₂, htb, ty, ⟨-, -⟩, hcode⟩ := h
            intro ρs ρo v ha hs hv
            rw [← hcode] at hv
            obtain ⟨w, hw, ht⟩ := optionTestOf_eval m fuel hn hs
            have hso : ρo.lookup name = some w := by rw [← ha]; exact hw
            have hvalid : kind = .nullable → w ≠ .undefined := by
              intro hk hu
              subst kind
              subst w
              simp [IR.Expr.eval, hso] at hv
            have ht := ht hvalid
            have hs' : Scoped m (env.narrow name value) ρs :=
              ⟨fun x => by rw [narrow_has]; exact hs.1 x, hs.2⟩
            have hsa : Scoped m (if isEq then env else env.narrow name value) ρs := by
              cases isEq <;> assumption
            have hsb : Scoped m (if isEq then env.narrow name value else env) ρs := by
              cases isEq <;> assumption
            have ra := fun u hu => ihE _ _ _ _ _ _ hta ρs ρo u ha hsa hu
            have rb := fun u hu => ihE _ _ _ _ _ _ htb ρs ρo u ha hsb hu
            rw [Eval.eval, ht]
            cases isEq <;> cases kind <;> cases w <;>
            simp [IR.Expr.eval, hso, nullTestVal, Val.truthy, eval_value, eval_into] at hv ⊢
            all_goals first | exact ra v hv | exact rb v hv
      | new sp callee typeArgs args =>
        simp only [translateExprCore] at h
        exact translateNew_sound m fs fuel (fun _ _ _ _ _ hx => ihE _ _ _ _ _ _ hx) h
      | _ => simp [translateExprCore] at h
    · intro env exp e ctx c ctx' h
      simp only [translateExpr, bind_ok, pure_ok] at h
      obtain ⟨c₀, s₁, h₀, rfl, -⟩ := h
      intro ρs ρo v ha hs hv
      rw [eval_into] at hv
      exact ihX _ _ _ _ _ _ h₀ ρs ρo v ha hs hv
    · intro env exp sp es ctx r ctx' h
      simp only [translateElements] at h
      simp at h
      obtain ⟨codes, s₁, hcodes, elem, s₂, -, _, s₃, -, unions, ⟨-, -⟩, hr⟩ := h
      rw [← hr]
      intro ρs ρo vs ha hs hvalues
      rw [evalList_into_value fs fuel unions.unions (some elem) ρo] at hvalues
      exact mapM_sim m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h)
        es ctx codes s₁ hcodes ρs ρo vs ha hs hvalues
    · intro env exp sp es ctx c ctx' h
      simp only [translateArray, ite_state] at h
      split at h
      · exact translateSpreadArray_sound m fs fuel (fun _ _ _ _ _ hx => ihE _ _ _ _ _ _ hx) h
      simp at h
      obtain ⟨values, elem, hel, hcode⟩ := h
      intro ρs ρo v ha hs hv
      rw [← hcode] at hv
      simp only [IR.Expr.eval] at hv
      cases hx : IR.Expr.evalList fs fuel ρo values with
      | none => simp [hx] at hv
      | some xs =>
        simp [hx] at hv
        subst hv
        have := ihL _ _ _ _ _ _ _ hel ρs ρo xs ha hs hx
        simp [Eval.eval, evalElems_of_evalList m fuel this]
    · exact translateCall_sound m fs fuel hc ihE
    · intro env exp sp props ctx c ctx' h
      exact translateObject_sound m fs fuel ihE ihO h
    · exact translateBinary_sound m fs fuel ihE
    · intro env exp s recv method args ctx c ctx' h sp name hname
      exact translateArrayMethod_sound m fs fuel ihE h hname
    · intro env exp s recv args ctx c ctx' h sp
      exact translateReduce_sound m fs fuel ihE h
    · intro env s recv method args ctx c ctx' h hmethod sp
      exact translateSort_sound m fs fuel ihE h hmethod
    · intro env s recv op args ctx c ctx' h sp name hname
      exact translateMapMethod_sound m fs fuel ihE h hname
    · intro env s recv method args ctx c ctx' h sp hr
      exact translateArrayCall_sound m fs fuel ihE h hr
    · intro env s o elem key ctx c ctx' h sp obj hobj
      exact translateArrayIndex_sound m fs fuel ihE h hobj
    · intro env s base rest ctx c ctx' h sp
      exact translateSpread_sound m fs fuel ihE h

end tolean.TypeScript.Proof
