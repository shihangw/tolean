import tolean.TypeScript.Proof.Expr

/-!
The head of a loop means what the output's list of items means.

`translateLoop` translates `for (const x of xs)` and the counted
`for (let i = a; i < b; i++)` in the same way: as a fold over a list. Only
the head differs, which `loopHead` translates. `loopHead_sim` states that the
interpreter runs the loop's body once for each value of that list, as
`Eval.execLoop` runs it. `Proof/Stmt.lean` then proves the body and the fold
once for both loops.
-/
namespace tolean.TypeScript.Proof
open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate
open tolean.TypeScript.Eval (Val Outcome)

variable {N : Type} [JSNumber N]

@[simp] theorem fuelLimit_ok {s s' : Ctx} {n : Nat} : fuelLimit s = .ok n s' ↔ n = s.fuel ∧ s' = s := by
  simp only [fuelLimit, bind_ok, get_ok, pure_ok]
  constructor
  · rintro ⟨c, s₁, ⟨rfl, rfl⟩, rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩

/-- `loopItems` reads no state, and gives what `loopOver` gives. -/
theorem loopItems_ok {iterable : Expr} {body : Stmt} {items : Code} {r : Ty × IR.Expr}
    {ctx ctx' : Ctx} (h : loopItems iterable body items ctx = .ok r ctx') :
    Stmt.mutatesIterable iterable body = false ∧ loopOver items = some r ∧ ctx' = ctx := by
  unfold loopItems at h
  simp only [ite_state] at h
  split at h
  · simp at h
  · rename_i hm
    simp only [pure_bind, orReject_ok] at h
    exact ⟨by simpa using hm, h.1, h.2.symm⟩

omit [JSNumber N] in
@[simp] theorem LoopHead.constAssignedIn_stmt {head : LoopHead} {s : Span} {b : Stmt} {rest : List Stmt} :
    (head.stmt s b).constAssignedIn rest = false := by
  cases head <;> simp [LoopHead.stmt]

variable (m : Eval.Scope) (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)

/-- The loop statement `stmt` runs its body `b`, with `x` bound to each value
of the list that the output's `items` gives. -/
def HeadSim (env : Translate.Env) (stmt : Stmt) (x : String) (b : Stmt) (items : IR.Expr) : Prop :=
  ∀ (ρs ρo : Eval.Env N) (vs : List (Val N)), Agree ρs ρo → Scoped m env ρs →
    IR.Expr.eval fs fuel ρo items = some (.list vs) →
    Eval.execStmt m fuel ρs stmt = Eval.execLoop m fuel ρs x b vs

/-- The head that `loopHead` translates runs the body over the items that it
gives. -/
theorem loopHead_sim (hc : CallsAgree (N := N) m.program fs fuel) {env : Translate.Env} {s : Span}
    {b : Stmt} {head : LoopHead} {x : String} {elemType : Ty} {li : IR.Expr} {ctx ctx' : Ctx}
    (h : loopHead env s b head ctx = .ok (x, elemType, li) ctx') :
    HeadSim (N := N) m fs fuel env (head.stmt s b) x b li := by
  cases head with
  | forOf kind element iterable =>
    simp only [loopHead, ite_state] at h
    split at h
    · rename_i hkind
      obtain rfl : kind = .const := by
        cases kind <;> first | rfl | simp +decide at hkind
      simp only [pure_bind, bind_ok, fuelLimit_ok] at h
      obtain ⟨_, _, ⟨rfl, rfl⟩, items, s₁, hitems, h⟩ := h
      obtain ⟨⟨elemType', li'⟩, s₁', hli, h⟩ := h
      obtain ⟨hmut, hlo, rfl⟩ := loopItems_ok hli
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h.1
      have hsimI := translateRecv_sim m fs fuel
        (fun _ _ _ hx => (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hx) hitems
      intro ρs ρo vs ha hs hi
      obtain ⟨vi, hvi, hiter⟩ := loopOver_sim m fs fuel hsimI hlo ha hs hi
      simp [LoopHead.stmt, Eval.execStmt, hmut, hvi, hiter]
    · simp at h
  | counted init test update =>
    simp only [loopHead, countedHead] at h
    split at h
    · rename_i name _ start _ _ n bound update
      simp only [ite_state] at h
      split at h
      · rename_i hshape
        simp only [pure_bind, ite_state] at h
        split at h
        rotate_left
        · simp at h
        split at h
        · simp at h
        · rename_i hch
          simp only [bind_ok, fuelLimit_ok] at h
          obtain ⟨_, _, ⟨rfl, rfl⟩, ca, s₁, hca, h⟩ := h
          split at h
          · rename_i hta
            simp only [bind_ok, fuelLimit_ok] at h
            obtain ⟨_, _, ⟨rfl, rfl⟩, cb, s₂, hcb, h⟩ := h
            split at h
            · simp only [pure_ok, Prod.mk.injEq] at h
              obtain ⟨⟨rfl, rfl, rfl⟩, -⟩ := h
              have hsa := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hca
              have hsb := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hcb
              intro ρs ρo vs ha hs hi
              obtain ⟨ws, hws, happ⟩ := out_ext fs fuel hi
              simp only [IR.Expr.evalList] at hws
              cases hxa : IR.Expr.eval fs fuel ρo ca.value with
              | none => simp [hxa] at hws
              | some wa =>
                cases hxb : IR.Expr.eval fs fuel ρo cb.value with
                | none => simp [hxa, hxb] at hws
                | some wb =>
                  simp only [hxa, hxb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                    Option.some.injEq] at hws
                  subst hws
                  rw [eval_value] at hxa hxb
                  have hva := hsa ρs ρo _ ha hs hxa
                  have hvb := hsb ρs ρo _ ha hs hxb
                  have hn : n = name ∧ update.incrementsName name = true := by simpa using hshape
                  obtain ⟨rfl, hinc⟩ := hn
                  cases wa <;> cases wb <;> simp [IR.ExprExt.apply] at happ
                  obtain ⟨l, hl, rfl⟩ := happ
                  simp [LoopHead.stmt, Eval.execStmt, hinc, hva, hvb, hl, hch]
            · simp at h
          · simp at h
      · simp at h
    · simp at h

end tolean.TypeScript.Proof
