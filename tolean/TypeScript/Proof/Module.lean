import tolean.TypeScript.Proof.Stmt

/-!
The translator is sound: a translated program computes only what the
TypeScript program computes.

`translate_sound` states it for a file. When `translateTree` parses a file
to the module `m` and translates it to `decls`, and a function of `decls`
gives a value for some arguments in the output's evaluator, then the
interpreter gives the same value for the same call of `m`. The theorem holds
for every model of numbers, every argument list and every fuel.

The proof discharges the hypothesis `CallsAgree` of the expression and
statement proofs. It goes by induction on the fuel: a call with fuel
`f + 1` runs the body with fuel `f`, so the statement theorem for the body
needs only the calls with fuel `f`. The functions of the output are the
translations of the source functions, in the same order and with the same
names and parameters, so a lookup by name finds the matching pair.

The theorem is about the output tree. A later step checks, for each file,
that the printed Lean computes what the output's evaluator says.
-/
namespace tolean.TypeScript.Proof

open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate
open tolean.TypeScript.Eval (Val Outcome)

/-- `R` holds for each pair of elements in the same place. -/
def Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Forall₂ R as bs
  | _, _ => False

theorem mapM_forall₂ {α β : Type} {f : α → TM β} :
    ∀ {l : List α} {s s' : Ctx} {out : List β}, l.mapM f s = .ok out s' →
      Forall₂ (fun a b => ∃ s₁ s₂, f a s₁ = .ok b s₂) l out
  | [], s, s', out, h => by
    simp [List.mapM_nil] at h
    obtain ⟨rfl, -⟩ := h
    trivial
  | a :: l, s, s', out, h => by
    simp [List.mapM_cons] at h
    obtain ⟨b, s₁, hb, bs, hbs, rfl⟩ := h
    exact ⟨⟨_, _, hb⟩, mapM_forall₂ hbs⟩

/-- The output function `out` is the translation of the source function
`src`: the same name, the same parameters, and a body that the translator
made from the source body, in a scope of exactly the parameters. -/
def FnRel (src : String × List String × Stmt) (out : String × List String × Output.Body) : Prop :=
  src.1 = out.1 ∧ src.2.1 = out.2.1 ∧
    ∃ F env ctx ctx', translateStatements F env .ret (blockStatements src.2.2) ctx = .ok out.2.2 ctx' ∧
      ∀ x, env.has x = decide (x ∈ src.2.1)

theorem params_fold {α : Type} {g : Env × List (String × α) × List Ty → Param → TM (Env × List (String × α) × List Ty)}
    (hstep : ∀ env lp ts p ctx r ctx', g (env, lp, ts) p ctx = .ok r ctx' →
      (∀ x, r.1.has x = (env.has x || x == p.name)) ∧ ∃ t, r.2.1 = lp ++ [(p.name, t)]) :
    ∀ (ps : List Param) (env : Env) lp ts ctx r ctx', ps.foldlM g (env, lp, ts) ctx = .ok r ctx' →
      (∀ x, r.1.has x = (env.has x || decide (x ∈ ps.map (·.name)))) ∧
        r.2.1.map (·.1) = lp.map (·.1) ++ ps.map (·.name) := by
  intro ps
  induction ps with
  | nil =>
    intro env lp ts ctx r ctx' h
    simp [List.foldlM_nil] at h
    obtain ⟨rfl, -⟩ := h
    simp
  | cons p ps ih =>
    intro env lp ts ctx r ctx' h
    simp only [List.foldlM_cons, bind_ok] at h
    obtain ⟨⟨env₁, lp₁, ts₁⟩, s₁, h₁, h⟩ := h
    obtain ⟨hhas, t, hlp⟩ := hstep _ _ _ _ _ _ _ h₁
    simp only at hhas hlp
    subst hlp
    obtain ⟨hhas', hlp'⟩ := ih _ _ _ _ _ _ h
    refine ⟨fun x => ?_, by simp [hlp']⟩
    rw [hhas', hhas]
    by_cases hx : x = p.name
    · subst hx; simp
    · have : (x == p.name) = false := by simpa using hx
      simp [this, hx]

theorem function_rel {sp : Span} {name : String} {params : List Param} {ret : Option TypeExpr}
    {body : Stmt} {ctx ctx' : Ctx} {o : Output.Decl}
    (h : translateFunction sp name params ret body ctx = .ok o ctx') :
    ∃ lp r b, o = .function name lp r b ∧ FnRel (name, params.map (·.name), body) (name, lp.map (·.1), b) := by
  unfold translateFunction at h
  cases ret with
  | none => simp at h
  | some returnType =>
    simp only [bind_ok] at h
    obtain ⟨name', s₁, hname, u, s₂, htop, ⟨env, lp, ts⟩, s₃, hfold, h⟩ := h
    obtain ⟨rfl, -⟩ := checkName_ok hname
    have hps := params_fold (hstep := fun env lp ts p ctx r ctx' hg => by
        simp only [bind_ok, orReject_ok, ite_state] at hg
        obtain ⟨type, s₁, ⟨-, rfl⟩, pn, s₂, hpn, hg⟩ := hg
        obtain ⟨rfl, -⟩ := checkName_ok hpn
        split at hg
        · simp at hg
        · simp only [pure_bind, bind_ok, pure_ok] at hg
          obtain ⟨ty, s₃, -, rfl, -⟩ := hg
          refine ⟨fun x => ?_, _, rfl⟩
          rw [has_add]
          by_cases hx : x = p.name
          · subst hx; simp
          · have h1 : (p.name == x) = false := by simpa using Ne.symm hx
            have h2 : (x == p.name) = false := by simpa using hx
            simp [h1, h2]) params _ _ _ _ _ _ hfold
    simp only [modify_ok, fuelLimit_ok, pure_ok] at h
    obtain ⟨r, s₄, -, _, _, rfl, _, _, ⟨rfl, rfl⟩, out, s₅, hout, _, _, rfl, rfl, -⟩ := h
    refine ⟨lp, r.lean, out, rfl, rfl, ?_, _, env, _, _, hout, fun x => ?_⟩
    · simpa using hps.2.symm
    · rw [hps.1 x]; simp [Env.has, Env.lookup]

theorem interface_struct {sp : Span} {name : String} {fields : List Field} {ctx ctx' : Ctx}
    {o : Output.Decl} (h : translateInterface sp name fields ctx = .ok o ctx') :
    ∃ n fs, o = .struct n fs := by
  unfold translateInterface at h
  simp only [bind_ok, modify_ok, pure_ok] at h
  obtain ⟨_, _, -, _, _, -, _, _, -, _, _, -, rfl, -⟩ := h
  exact ⟨_, _, rfl⟩

/-- The source and output declarations, in the same order. -/
theorem decls_rel {m : Module} {ctx ctx' : Ctx} {decls : List Output.Decl}
    (h : translateDecls m ctx = .ok decls ctx') :
    Forall₂ FnRel (Eval.functions m) (Output.functions decls) := by
  have hall := mapM_forall₂ h
  clear h
  unfold Eval.functions Output.functions
  generalize m.decls = ds at hall
  induction ds generalizing decls with
  | nil =>
    cases decls with
    | nil => trivial
    | cons _ _ => exact hall.elim
  | cons d ds ih =>
    cases decls with
    | nil => exact hall.elim
    | cons o os =>
      obtain ⟨⟨s₁, s₂, hd⟩, hrest⟩ := hall
      cases d with
      | interface sp ex name fields =>
        obtain ⟨n, fs, rfl⟩ := interface_struct hd
        simpa [List.filterMap_cons] using ih hrest
      | function sp ex name params ret body =>
        obtain ⟨lp, r, b, rfl, hrel⟩ := function_rel hd
        simp only [List.filterMap_cons]
        exact ⟨hrel, ih hrest⟩
      | _ => simp at hd

theorem lookup_rel :
    ∀ {srcs : List (String × List String × Stmt)} {outs : List (String × List String × Output.Body)},
      Forall₂ FnRel srcs outs → ∀ {name : String} {ps : List String} {b : Output.Body},
        outs.lookup name = some (ps, b) →
        ∃ bS, srcs.lookup name = some (ps, bS) ∧ FnRel (name, ps, bS) (name, ps, b)
  | [], [], _, _, _, _, h => by simp at h
  | (n, ps', bS) :: srcs, (n', ps'', b') :: outs, ⟨⟨hn, hps, hrel⟩, hrest⟩, name, ps, b, h => by
    simp only at hn hps
    subst hn hps
    simp only [List.lookup] at h ⊢
    by_cases hk : name = n
    · subst hk
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨bS, by simp, rfl, rfl, hrel⟩
    · have : (name == n) = false := by simpa using hk
      simp only [this] at h ⊢
      exact lookup_rel hrest h
  | [], _ :: _, h, _, _, _, _ | _ :: _, [], h, _, _, _, _ => h.elim

theorem lookup_isSome {β : Type} (x : String) (l : List (String × β)) :
    (l.lookup x).isSome = decide (x ∈ l.map Prod.fst) := by
  rw [Bool.eq_iff_iff, List.lookup_isSome_iff]
  simp only [decide_eq_true_eq, List.mem_map, beq_iff_eq]
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩⟩

variable {N : Type} [JSNumber N]

omit [JSNumber N] in
theorem scoped_params {env : Translate.Env} {ps : List String} {vs : List (Val N)}
    (henv : ∀ x, env.has x = decide (x ∈ ps)) (hlen : ps.length = vs.length) :
    Scoped env ((ps.zip vs).reverse) := fun x => by
  rw [lookup_isSome, henv, List.map_reverse, List.map_fst_zip (by omega)]
  simp

variable (m : Module) (fs : List (String × List String × Output.Body))

/-- Every call of the output gives what the same call of the source gives,
for every fuel. -/
theorem calls_agree (hrel : Forall₂ FnRel (Eval.functions m) fs) :
    ∀ fuel, CallsAgree (N := N) m fs fuel
  | 0 => fun name vs v h => by simp [callO] at h
  | fuel + 1 => fun name vs v h => by
    have hc := calls_agree hrel fuel
    simp only [callO] at h
    cases hl : fs.lookup name with
    | none => simp [hl] at h
    | some pb =>
      obtain ⟨ps, b⟩ := pb
      simp only [hl, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · simp at h
      · rename_i hlen
        cases hb : Output.Body.exec fs fuel (ps.zip vs).reverse b with
        | none => simp [hb] at h
        | some o =>
          cases o with
          | normal _ => simp [hb] at h
          | ret w =>
            simp [hb] at h
            subst h
            obtain ⟨bS, hlS, -, -, F, env, ctx, ctx', htr, henv⟩ := lookup_rel hrel hl
            have hlen' : ps.length = vs.length := by simpa using hlen
            have hsim := (stmts_sound m fs fuel hc F).1 _ _ _ _ _ _ htr
            have hex := (hsim _ _ (fun _ => rfl) (scoped_params henv hlen')).1 w hb
            have hst := block_ret m fuel bS hex
            simp [callS, hlS, hlen', hst]

variable {m} in
/-- When the translator translates a module, a call of a function of the
output gives a value only when the interpreter gives the same value for the
same call of the source, for all arguments and all fuel. -/
theorem run_sound {ctx ctx' : Ctx} {decls : List Output.Decl} (h : translateDecls m ctx = .ok decls ctx')
    (name : String) (args : List (Val N)) (fuel : Nat) (v : Val N)
    (hv : Output.run decls name args fuel = some v) : Eval.run m name args fuel = some v :=
  calls_agree m (Output.functions decls) (decls_rel h) (fuel + 1) name args v hv

/-- The same, for a file: when `translateTree` parses and translates the file
to `decls`, each function of `decls` computes what the interpreter computes
for the parsed module `m`. -/
theorem translate_sound {file source : String} {target : Edition} {m : Module} {names : Output.Names}
    {decls : List Output.Decl} (h : translateTree file source target = .ok (m, names, decls))
    (name : String) (args : List (Val N)) (fuel : Nat) (v : Val N)
    (hv : Output.run decls name args fuel = some v) : Eval.run m name args fuel = some v := by
  unfold translateTree at h
  cases hp : parse source target with
  | error e => simp [hp, Except.mapError] at h; cases h
  | ok m' =>
    simp only [hp, Except.mapError, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i decls' s heq
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact run_sound heq name args fuel v hv

end tolean.TypeScript.Proof
