import tolean.Go.Proof.Stmt

/-!
The translation of a package's pure functions means what the functions mean.

`translate_sound` states it for `translateFuncs`: when a function of the
output gives a value for a call, the interpreter gives the same value for the
same call of the source's function. It holds for every package, every order,
every input and every amount of fuel. The translator never fails as a whole,
because it leaves out each function that it refuses, so the theorem needs no
hypothesis about it.

The theorem is about the IR, so a package still trusts the printer: the
printed Lean computes what the IR's evaluator gives, and the evaluator gives
a value where the printed Lean does. It also trusts the parser, which
`tests/go/check` tests against `go/parser`.
-/
namespace tolean.Go.Proof

open tolean.Go tolean.Go.Syntax tolean.Go.Pure
open tolean.Go.Eval (Val Outcome)

/-! ### Functions -/

theorem paramList_names {ctx : Ctx} :
    ∀ {fields : List Field} {ps : List (String × Ty)}, paramList ctx fields = some ps →
      ps.map (·.1) = Eval.paramNames fields
  | [], ps, h => by
    simp only [paramList, Option.some.injEq] at h
    subst h
    simp [Eval.paramNames]
  | .mk sp names te tag :: rest, ps, h => by
    simp only [paramList] at h
    cases ht : resolveType ctx te with
    | none => simp [ht] at h
    | some t =>
      cases hr : paramList ctx rest with
      | none => simp [ht, hr] at h
      | some ps' =>
        simp only [ht, hr, Option.bind_eq_bind, Option.bind_some] at h
        change some _ = some ps at h
        simp only [Option.some.injEq] at h
        subst h
        have := paramList_names hr
        simp only [Eval.paramNames] at this ⊢
        simp [this, Function.comp_def]

/-- What `translateFunc` gives for a function that it accepts. -/
theorem translateFunc_ok {ctx : Ctx} {d : Decl} {decl : IR.Decl} {sig : FnSig}
    (h : translateFunc ctx d = .ok (decl, sig)) :
    ∃ sp name fields results bsp body, ∃ (ps : List (String × Ty)) (result : Ty) (b : IR.Body),
      d = .func sp none name fields results (.block bsp body) ∧
      ps.map (·.1) = Eval.paramNames fields ∧
      decl = .function name (ps.map fun (n, t) => (n, t.lean)) result.lean b ∧
      sig.name = name ∧
      translateStmts ctx (ps.map fun (n, t) => Local.mk n t) (.ret result) stmtFuel body = .ok b := by
  unfold translateFunc at h
  split at h
  · next sp name params rsp rt bsp body =>
    tm_simp at h
    obtain ⟨-, h⟩ := h
    cases hps : paramList ctx params with
    | none => simp [hps, reject, throw, throwThe, MonadExceptOf.throw] at h
    | some ps =>
      cases hr : resolveType ctx rt with
      | none => simp [hps, hr, reject, throw, throwThe, MonadExceptOf.throw] at h
      | some result =>
        simp only [hps, hr] at h
        tm_simp at h
        obtain ⟨-, -, b, hb, rfl, rfl⟩ := h
        exact ⟨sp, name, params, _, bsp, body, ps, result, b, rfl, paramList_names hps, rfl, rfl, hb⟩
  · exact absurd h reject_ne_ok
  · exact absurd h throw_ne_ok

/-- The function that `findFunc` finds is the one that a call finds. -/
theorem findFunc_lookup :
    ∀ {decls : List Decl} {name : String} {sp : Span} {r : Option (List Field)} {n : String}
      {fields : List Field} {results : Option (List Field)} {body : Stmt},
      findFunc decls name = some (.func sp r n fields results body) →
      (Eval.program decls).funcs.lookup name = some (Eval.paramNames fields, body)
  | [], _, _, _, _, _, _, _, h => by simp [findFunc] at h
  | d :: ds, name, sp, r, n, fields, results, body, h => by
    simp only [findFunc, List.find?_cons] at h
    simp only [Eval.program, List.filterMap_cons]
    split at h
    · next hd =>
      simp only [Option.some.injEq] at h
      subst h
      cases r with
      | some _ => simp at hd
      | none =>
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
          Bool.or_eq_false_iff] at hd
        obtain ⟨rfl, h1, h2⟩ := hd
        simp [Eval.funcOf, h1, h2]
    · next hd =>
      have ih := findFunc_lookup (decls := ds) h
      simp only [Eval.program] at ih
      cases d with
      | gen _ => simpa [Eval.funcOf] using ih
      | func sp' r' n' fields' results' body' =>
        cases r' with
        | some _ => simpa [Eval.funcOf] using ih
        | none =>
          have hd' : (n' == name && !(n' == "init" || n' == "_")) = false := hd
          by_cases hi : (n' == "init" || n' == "_") = true
          · simpa [Eval.funcOf, hi] using ih
          · have hne : n' ≠ name := by
              intro heq; subst heq; simp [hi] at hd'
            have hne' : (name == n') = false := by simpa using Ne.symm hne
            simp [Eval.funcOf, hi, List.lookup, hne', ih]

/-! ### The output's functions -/

theorem lookup_functions {key : DeclRef} {x : List String × IR.Body} :
    ∀ {decls : List IR.Decl}, (IR.functions decls).lookup key = some x →
      ∃ name params ret body, IR.Decl.function name params ret body ∈ decls ∧
        key = ⟨"", name⟩ ∧ x = (params.map (·.1), body)
  | [], h => by simp [IR.functions] at h
  | d :: ds, h => by
    cases d with
    | function name params ret body =>
      simp only [IR.functions, List.filterMap_cons, List.lookup] at h
      split at h
      · next hk =>
        simp only [Option.some.injEq] at h
        exact ⟨name, params, ret, body, List.mem_cons_self .., by cases key; simpa using hk, h.symm⟩
      · obtain ⟨n, ps, r, b, hm, hk, hx⟩ := lookup_functions (decls := ds) h
        exact ⟨n, ps, r, b, List.mem_cons_of_mem _ hm, hk, hx⟩
    | _ =>
      simp only [IR.functions, List.filterMap_cons] at h
      obtain ⟨n, ps, r, b, hm, hk, hx⟩ := lookup_functions (decls := ds) h
      exact ⟨n, ps, r, b, List.mem_cons_of_mem _ hm, hk, hx⟩

/-- Each function of the output is the translation of the function that a
call of its name finds. -/
def Accepted (decls : List Decl) (out : List (IR.Decl × FnSig)) : Prop :=
  ∀ r ∈ out, ∃ d ks, findFunc decls r.2.name = some d ∧
    translateFunc ⟨Eval.program decls, ks⟩ d = .ok r

theorem translateFuncsFrom_accepted (decls : List Decl) :
    ∀ (order : List String) (acc : List (IR.Decl × FnSig)), Accepted decls acc →
      Accepted decls (translateFuncsFrom decls order acc)
  | [], acc, h => by simpa [translateFuncsFrom] using h
  | n :: ns, acc, h => by
    simp only [translateFuncsFrom]
    split
    · exact translateFuncsFrom_accepted decls ns acc h
    · split
      · exact translateFuncsFrom_accepted decls ns acc h
      · next d hd =>
        split
        · next r hr =>
          split
          · next hn =>
            refine translateFuncsFrom_accepted decls ns _ fun q hq => ?_
            rcases List.mem_append.mp hq with hq | hq
            · exact h q hq
            · simp only [List.mem_singleton] at hq
              subst hq
              have : q.2.name = n := by simpa using hn
              exact ⟨d, _, this ▸ hd, hr⟩
          · exact translateFuncsFrom_accepted decls ns acc h
        · exact translateFuncsFrom_accepted decls ns acc h

/-! ### Calls -/

theorem lookup_isSome (l : Eval.Env) (n : String) : (l.lookup n).isSome = (l.map (·.1)).contains n := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : n = k
    · subst hk; simp [List.lookup]
    · rw [lookup_cons_ne _ _ hk, ih]
      have : (n == k) = false := by simpa using hk
      simp [hk]

theorem has_map (ps : List (String × Ty)) (n : String) :
    Pure.Env.has (ps.map fun (x, t) => Local.mk x t) n = (ps.map (·.1)).contains n := by
  simp only [Pure.Env.has, Pure.Env.lookup, List.find?_map]
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨x, t⟩ := p
    by_cases hx : x = n
    · subst hx; simp
    · simp only [List.find?_cons, Function.comp_apply, List.map_cons, List.contains_cons]
      have : (x == n) = false := by simpa using hx
      simp only [this, ih]
      have : (n == x) = false := by simpa using Ne.symm hx
      simp [this]

/-- The interpreter's environment at the start of a call binds the names of
the parameters. -/
theorem scoped_params (ps : List (String × Ty)) (vs : List Val) (hlen : ps.length = vs.length) :
    Scoped (ps.map fun (x, t) => Local.mk x t) ((ps.map (·.1)).zip vs).reverse := by
  intro n
  rw [lookup_isSome, has_map, List.map_reverse, List.map_fst_zip (by simp [hlen])]
  simp

/-- A call of the output that gives a value finds the function, passes as
many arguments as it has parameters, and its body returns the value. -/
theorem callO_some {fs : Funcs} {fuel : Nat} {ref : DeclRef} {vs : List Val} {v : Val}
    (h : callO fs (fuel + 1) ref vs = some v) :
    ∃ ps b, fs.lookup ref = some (ps, b) ∧ ps.length = vs.length ∧
      IR.Body.exec fs fuel (ps.zip vs).reverse b = some (.ret v) := by
  simp only [callO] at h
  cases hl : fs.lookup ref with
  | none => simp [hl] at h
  | some x =>
    obtain ⟨ps, b⟩ := x
    refine ⟨ps, b, rfl, ?_⟩
    by_cases hlen : ps.length = vs.length
    · refine ⟨hlen, ?_⟩
      cases hex : IR.Body.exec fs fuel (ps.zip vs).reverse b with
      | none => simp [hl, hlen, hex] at h
      | some o =>
        cases o with
        | normal _ => simp [hl, hlen, hex] at h
        | ret w => simp [hl, hlen, hex] at h; rw [h]
    · simp [hl, hlen] at h

theorem callS_of {p : Eval.Program} {fuel : Nat} {f : String} {vs : List Val} {v : Val}
    {ps : List String} {st : Stmt} (hl : p.funcs.lookup f = some (ps, st)) (hlen : ps.length = vs.length)
    (hex : Eval.execStmt p fuel (ps.zip vs).reverse st = some (.ret v)) :
    callS p (fuel + 1) f vs = some v := by
  simp [callS, hl, hlen, hex]

variable (decls : List Decl) (order : List String)

/-- Every call of the output agrees with the interpreter, by induction on the
fuel: a call at `fuel + 1` runs a body whose calls have `fuel`. -/
theorem calls_agree : ∀ fuel, CallsAgree (Eval.program decls)
    (IR.functions ((translateFuncs decls order).map (·.1))) fuel
  | 0 => fun f vs v h => by simp [callO] at h
  | fuel + 1 => fun f vs v h => by
    have ih := calls_agree fuel
    obtain ⟨psO, b, hl, hlen, hex⟩ := callO_some h
    obtain ⟨n, params, ret, b'', hmem, hkey, hx⟩ := lookup_functions hl
    simp only [DeclRef.mk.injEq, true_and] at hkey
    subst hkey
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    obtain ⟨r, hr, hr1⟩ := List.mem_map.mp hmem
    obtain ⟨d, ks, hfind, htr⟩ := translateFuncsFrom_accepted decls order [] (by simp [Accepted]) r hr
    obtain ⟨sp, name, fields, results, bsp, body, ps, result, b', rfl, hnames, hdecl, hsig, hstmts⟩ :=
      translateFunc_ok htr
    rw [hr1] at hdecl
    simp only [IR.Decl.function.injEq] at hdecl
    obtain ⟨rfl, rfl, -, rfl⟩ := hdecl
    rw [hsig] at hfind
    have hsim := stmts_sound (Eval.program decls) _ fuel (ctx := ⟨Eval.program decls, ks⟩) rfl ih hstmts
    have hps : List.map (fun x => x.fst) (List.map (fun x : String × Ty => (x.1, x.2.lean)) ps) =
        ps.map (·.1) := by simp
    rw [hps] at hlen hex
    have hlen' : ps.length = vs.length := by simpa using hlen
    have hbody := (hsim _ _ (Agree.refl _) (scoped_params ps vs hlen')).1 v hex
    refine callS_of (findFunc_lookup hfind) (by rw [← hnames]; exact hlen) ?_
    rw [← hnames, execStmt_block, hbody]
    rfl

/-- The pure functions that the translator writes as IR mean what the
source's functions mean: a call of one of them gives a value only when the
interpreter gives the same value for the same call. -/
theorem translate_sound (name : String) (args : List Val) (fuel : Nat) (v : Val)
    (hv : IR.runIn (IR.functions ((translateFuncs decls order).map (·.1))) ⟨"", name⟩ args fuel =
      some v) :
    Eval.runIn (Eval.program decls) name args fuel = some v := by
  have := calls_agree decls order (fuel + 1) name args v (by simpa [callO, IR.runIn] using hv)
  simpa [callS, Eval.runIn] using this

end tolean.Go.Proof
