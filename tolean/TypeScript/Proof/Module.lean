import tolean.TypeScript.Proof.Stmt

/-!
The translator is sound: a translated program computes only what the
TypeScript program computes.

`program_sound` states it for a program of several files, and
`translate_sound` for one file. When the translator translates every file of
a program, each file after the files it imports from, and a function of the
Tolean IR gives a value for some arguments in the IR's evaluator, then the
interpreter gives the same value for the same call of the program. The
theorem holds for every model of numbers, every argument list and every fuel.

Three facts make it work.

- A call in the output names its function by its file and its name, and the
  interpreter resolves a call to the same pair. `module_resolves` shows that
  each function the translator lets a call name is the one the interpreter
  calls: the file's own function, or the exported function of the file it is
  imported from. It needs the interfaces of the earlier files to be
  `Faithful`: they offer only functions that those files export.
- The functions of the output are the translations of the program's
  functions, in the same order and under the same keys, so a lookup by key
  finds the matching pair.
- `calls_agree` discharges the hypothesis `CallsAgree` of the expression and
  statement proofs by induction on the fuel. A call with fuel `f + 1` runs
  the body with fuel `f`, so the statement theorem for the body needs only
  the calls with fuel `f`.

The theorem is about the Tolean IR. The printer link is trusted: that the
printed Lean computes what the IR's evaluator gives. A certificate proves
the link for its file, with `Proof/Link.lean`.
-/
namespace tolean.TypeScript.Proof

open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate
open tolean.TypeScript.Eval (Val Outcome)

/-! ### What a declaration does to the state -/

section State

variable {α : Type}

@[simp] theorem set_ok {c s s' : Ctx} {u : PUnit} : (set c : TM PUnit) s = .ok u s' ↔ s' = c := by
  simp [set, MonadStateOf.set, EStateM.set]
  exact eq_comm

theorem isolated_ok {x : TM α} {s s' : Ctx} {a : α} (h : isolated x s = .ok a s') :
    s' = s ∧ ∃ s₁, x s = .ok a s₁ := by
  simp only [isolated, bind_ok, get_ok, set_ok, pure_ok] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, r, s₂, hx, u, s₃, rfl, rfl, rfl⟩ := h
  exact ⟨rfl, s₂, hx⟩

theorem declareTopLevel_ok {sp : Span} {name : String} {s s' : Ctx} {u : Unit}
    (h : declareTopLevel sp name s = .ok u s') : s' = s ∧ ∀ f ∈ s.functions, f.name ≠ name := by
  simp only [declareTopLevel, bind_ok, get_ok, ite_state] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, h⟩ := h
  split at h
  · simp at h
  · rename_i hn
    simp only [pure_bind, ite_state] at h
    split at h
    · simp at h
    · simp only [pure_ok] at h
      refine ⟨h.2.symm, fun f hf heq => hn ?_⟩
      simp only [Ctx.taken, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inl (Or.inr ⟨f, hf, heq⟩)

/-- A name that the file declares at its top is one that it has not declared. -/
theorem declareTopLevel_fresh {sp : Span} {name : String} {s s' : Ctx} {u : Unit}
    (h : declareTopLevel sp name s = .ok u s') : s.taken name = false := by
  simp only [declareTopLevel, bind_ok, get_ok, ite_state] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, h⟩ := h
  split at h
  · simp at h
  · rename_i hn
    simp only [Bool.or_eq_true, not_or] at hn
    exact Bool.eq_false_iff.mpr hn.1

/-- A name that the file declares at its top is not an error class's. -/
theorem declareTopLevel_classes {sp : Span} {name : String} {s s' : Ctx} {u : Unit}
    (h : declareTopLevel sp name s = .ok u s') : ∀ c ∈ s.errorClasses, c.name ≠ name := by
  simp only [declareTopLevel, bind_ok, get_ok, ite_state] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, h⟩ := h
  split at h
  · simp at h
  · rename_i hn
    simp only [Bool.or_eq_true, not_or, List.any_eq_true, beq_iff_eq, not_exists, not_and] at hn
    exact hn.2

/-- A name that the file declares at its top is not a global's. -/
theorem declareTopLevel_global {sp : Span} {name : String} {s s' : Ctx} {u : Unit}
    (h : declareTopLevel sp name s = .ok u s') : isGlobalName name = false := by
  simp only [declareTopLevel, bind_ok, get_ok, ite_state] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, h⟩ := h
  split at h
  · simp at h
  · simp only [pure_bind, ite_state] at h
    split at h
    · simp at h
    · rename_i hg
      exact Bool.eq_false_iff.mpr hg

end State

/-- The functions that a declaration adds, as references: a function adds
itself, and an import adds each name that it imports as a value. -/
def declRefs (file : String) : Decl → List DeclRef
  | .function _ _ name _ _ _ _ => [⟨file, name⟩]
  | .import _ names source =>
    match Eval.resolvePath file source with
    | some target => (names.filter (!·.typeOnly)).map fun n => ⟨target, n.name⟩
    | none => []
  | _ => []

/-- The names that a declaration binds in its module: the name that it
declares, or each name that an import names. -/
def boundNames : Decl → List String
  | .function _ _ name _ _ _ _ | .interface _ _ name _ _ | .typeAlias _ _ name _ _ | .enum _ _ name _ => [name]
  | .import _ names _ => names.map (·.name)
  | _ => []

/-- A declaration that binds a name to an enum, or to what an import names,
binds that name. -/
theorem enumBinding_bound {P : Eval.Program} {file x : String} {d : Decl}
    (h : (Eval.enumBinding P file x d).isSome) : x ∈ boundNames d := by
  cases d with
  | enum sp ex n ms =>
    simp only [Eval.enumBinding] at h
    split at h
    · rename_i hn; simp only [beq_iff_eq] at hn; simp [boundNames, hn]
    · simp at h
  | «import» sp names source =>
    simp only [Eval.enumBinding] at h
    split at h
    · rename_i hany
      obtain ⟨n, hn, hx⟩ := List.any_eq_true.mp hany
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      simp only [boundNames, List.mem_map]
      exact ⟨n, hn, hx.2⟩
    · simp at h
  | _ => simp [Eval.enumBinding] at h

/-- Two declarations of a module that bind one name are one declaration, when
the module binds each name once. -/
theorem bound_unique {ds : List Decl} (h : (ds.flatMap boundNames).Nodup) {a b : Decl} (ha : a ∈ ds)
    (hb : b ∈ ds) {x : String} (hxa : x ∈ boundNames a) (hxb : x ∈ boundNames b) : a = b := by
  induction ds with
  | nil => simp at ha
  | cons d ds ih =>
    simp only [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨_, h2, h3⟩ := h
    rcases List.mem_cons.mp ha with ha₁ | ha₁ <;> rcases List.mem_cons.mp hb with hb₁ | hb₁
    · rw [ha₁, hb₁]
    · subst ha₁; exact absurd rfl (h3 _ hxa _ (List.mem_flatMap.mpr ⟨b, hb₁, hxb⟩))
    · subst hb₁; exact absurd rfl (h3 _ hxb _ (List.mem_flatMap.mpr ⟨a, ha₁, hxa⟩))
    · exact ih h2 ha₁ hb₁

/-- The interfaces name the files they come from. -/
def IfacesSelf (ifaces : List (String × Interface)) : Prop :=
  ∀ t i, ifaces.lookup t = some i → ∀ g ∈ i.functions, g.file = t

theorem params_fold {α : Type}
    {g : Env × List (String × α) × List Ty → Param → TM (Env × List (String × α) × List Ty)}
    (hstep : ∀ env lp ts p ctx r ctx', g (env, lp, ts) p ctx = .ok r ctx' →
      (∀ x, r.1.has x = (env.has x || x == p.name)) ∧ globals r.1 = globals env ∧
        ∃ t, r.2.1 = lp ++ [(p.name, t)]) :
    ∀ (ps : List Param) (env : Env) lp ts ctx r ctx', ps.foldlM g (env, lp, ts) ctx = .ok r ctx' →
      (∀ x, r.1.has x = (env.has x || decide (x ∈ ps.map (·.name)))) ∧ globals r.1 = globals env ∧
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
    obtain ⟨hhas, hfns, t, hlp⟩ := hstep _ _ _ _ _ _ _ h₁
    simp only at hhas hfns hlp
    subst hlp
    obtain ⟨hhas', hfns', hlp'⟩ := ih _ _ _ _ _ _ h
    refine ⟨fun x => ?_, hfns'.trans hfns, by simp [hlp']⟩
    rw [hhas', hhas]
    by_cases hx : x = p.name
    · subst hx; simp
    · have : (x == p.name) = false := by simpa using hx
      simp [this, hx]

/-- The checks of a function's type parameters change nothing. -/
theorem checkTypeParams_ok {sp : Span} {named : String → Bool} :
    ∀ {seen vs : List String} {s s' : Ctx} {u : Unit}, checkTypeParams sp named seen vs s = .ok u s' → s' = s
  | _, [], _, _, _, h => by
    simp only [checkTypeParams, pure_ok] at h
    exact h.2.symm
  | _, v :: vs, _, _, _, h => by
    simp only [checkTypeParams, bind_ok] at h
    obtain ⟨_, s₁, hn, h⟩ := h
    obtain ⟨-, rfl⟩ := checkName_ok hn
    simp only [ite_state] at h
    split at h
    · simp at h
    · simp only [pure_bind, bind_ok, get_ok] at h
      obtain ⟨c, s₂, ⟨rfl, rfl⟩, h⟩ := h
      simp only [ite_state] at h
      split at h
      · simp at h
      · split at h
        · try simp only [pure_bind] at h
          exact checkTypeParams_ok h
        · simp at h

/-- What a function declaration does: it adds itself to the functions, and its
body is the translation of the source body, in a scope of its parameters and
of the functions declared before it. -/
theorem translateFunction_ok {thr : String → Bool} {cls : String → Option (Option (List CtorParam × Expr))}
    {classes : List ClassInfo} {sp : Span} {ex : Bool} {name : String} {tps : List String}
    {params : List Param} {ret : Option TypeExpr} {body : Stmt} {s s' : Ctx} {o : IR.Decl}
    (h : translateFunction thr cls classes sp ex name tps params ret body s = .ok o s') :
    (s'.structs, s'.aliases, s'.enums, s'.unions, s'.enumValues) =
      (s.structs, s.aliases, s.enums, s.unions, s.enumValues) ∧ s.taken name = false ∧
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧
      (∀ g ∈ s.functions, g.name ≠ name) ∧
      ∃ f, s'.functions = s.functions ++ [f] ∧ f.file = s.file ∧ f.name = name ∧ f.exported = ex ∧
      ∃ lp r out, o = .function name lp r out ∧ lp.map (·.1) = params.map (·.name) ∧
        ∃ F env c c', translateStatements F env .ret (blockStatements (Eval.Stmt.hoisted thr cls body)) c = .ok out c' ∧
          env.functions = s.functions ++ [f] ∧ env.enums = s.enumValues ∧ env.classes = classes ∧
          (∀ x, env.has x = decide (x ∈ params.map (·.name))) ∧
          Stmt.ownsChanges (params.map (·.name)) (Eval.Stmt.hoisted thr cls body) = true := by
  unfold translateFunction at h
  cases ret with
  | none => simp at h
  | some returnType =>
    simp only [bind_ok] at h
    obtain ⟨name', s₁, hname, u, s₂, htop, u₁, s₂', hcheck, u₂, s₂'', hscope, c, s₃, hget, ⟨env, lp, ts⟩, s₄,
      hfold, h⟩ := h
    obtain ⟨rfl, rfl⟩ := checkName_ok hname
    have htaken := declareTopLevel_fresh htop
    obtain ⟨rfl, hfresh⟩ := declareTopLevel_ok htop
    obtain rfl := checkTypeParams_ok hcheck
    simp only [modify_ok] at hscope
    subst hscope
    simp only [get_ok] at hget
    obtain ⟨rfl, rfl⟩ := hget
    obtain ⟨rfl, s₅, hfold⟩ := isolated_ok hfold
    have hps := params_fold (hstep := fun env lp ts p ctx r ctx' hg => by
        simp only [bind_ok, orReject_ok, ite_state] at hg
        obtain ⟨type, s₁, ⟨-, rfl⟩, pn, s₂, hpn, hg⟩ := hg
        obtain ⟨rfl, -⟩ := checkLocalName_ok hpn
        split at hg
        · simp at hg
        · simp only [pure_bind, bind_ok, pure_ok] at hg
          obtain ⟨ty, s₃, -, rfl, -⟩ := hg
          refine ⟨fun x => ?_, rfl, _, rfl⟩
          rw [has_add]
          by_cases hx : x = p.name
          · subst hx; simp
          · have h1 : (p.name == x) = false := by simpa using Ne.symm hx
            have h2 : (x == p.name) = false := by simpa using hx
            simp [h1, h2]) params _ _ _ _ _ _ hfold
    simp only [modify_ok, fuelLimit_ok] at h
    obtain ⟨r, s₆, hr, _, s₇, rfl, _, _, ⟨rfl, rfl⟩, out, s₈, hbody, h⟩ := h
    -- The check that a call of the function itself passes a part of a
    -- parameter only refuses.
    split at h
    · rw [bind_ok] at h; obtain ⟨_, _, h, -⟩ := h; exact absurd h (reject_ne_ok _ _ _ _ _)
    simp only [pure_bind] at h
    -- So does the check that the function changes only collections it owns.
    split at h
    · rw [bind_ok] at h; obtain ⟨_, _, h, -⟩ := h; exact absurd h (reject_ne_ok _ _ _ _ _)
    rename_i hown
    simp only [bind_ok, modify_ok, pure_ok] at h
    obtain ⟨_, s₉, rfl, rfl, rfl⟩ := h
    obtain ⟨rfl, -⟩ := isolated_ok hr
    obtain ⟨rfl, s₁₀, hbody⟩ := isolated_ok hbody
    have hg := hps.2.1
    simp only [globals, Prod.mk.injEq] at hg
    refine ⟨rfl, htaken, rfl, rfl, hfresh, _, rfl, rfl, rfl, rfl, lp, _, out, rfl, ?_, _, _, _, _, hbody,
      by simp [hg.1], hg.2.1, hg.2.2.1, fun x => ?_, by simpa using hown⟩
    · simpa using hps.2.2
    · have hx := hps.1 x
      simp only [Env.has, Env.lookup] at hx ⊢
      rw [hx]; simp

/-- A reference of an import's name stays one when the import names one more. -/
theorem import_refs_cons {target : String} {n : ImportName} {ns : List ImportName} {r : DeclRef}
    (h : r ∈ (ns.filter (!·.typeOnly)).map fun n => (⟨target, n.name⟩ : DeclRef)) :
    r ∈ ((n :: ns).filter (!·.typeOnly)).map fun n => (⟨target, n.name⟩ : DeclRef) := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
  obtain ⟨ha₁, ha₂⟩ := List.mem_filter.mp ha
  exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_cons_of_mem _ ha₁, ha₂⟩, rfl⟩

/-- What an import does: it adds functions for names that it imports as
values, from the file it names, and keeps the function names distinct. A name
that it imports as a value may also be a string enum, which adds no function. -/
theorem translateImport_ok {sp : Span} {names : List ImportName} {source : String} {s s' : Ctx}
    {u : Unit} (hself : IfacesSelf s.interfaces) (h : translateImport sp names source s = .ok u s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧
      ∃ more, s'.functions = s.functions ++ more ∧
        (∀ f ∈ more, f.ref ∈ declRefs s.file (.import sp names source)) ∧
        (∀ f ∈ more, f.exported = false) ∧
        ((s.functions.map (·.name)).Nodup → (s'.functions.map (·.name)).Nodup) ∧
        (∀ f ∈ more, ∃ i, s.interfaces.lookup f.file = some i ∧ ∃ g ∈ i.functions, g.name = f.name) := by
  unfold translateImport at h
  simp only [bind_ok, get_ok, orReject_ok] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, target, s₂, ⟨htarget, rfl⟩, iface, s₃, ⟨hiface, rfl⟩, hloop⟩ := h
  simp only [ite_state] at hloop
  split at hloop
  · simp at hloop
  rename_i hyear
  clear hyear
  simp only [pure_bind] at hloop
  have hgf := hself _ _ hiface
  simp only [declRefs, htarget]
  suffices key : s'.file = s₁.file ∧ s'.interfaces = s₁.interfaces ∧
      ∃ more, s'.functions = s₁.functions ++ more ∧
        (∀ f ∈ more, f.ref ∈ (names.filter (!·.typeOnly)).map (fun n => (⟨target, n.name⟩ : DeclRef))) ∧
        (∀ f ∈ more, f.exported = false) ∧
        ((s₁.functions.map (·.name)).Nodup → (s'.functions.map (·.name)).Nodup) ∧
        (∀ f ∈ more, f.file = target ∧ ∃ g ∈ iface.functions, g.name = f.name) by
    obtain ⟨hf, hi, more, hfns, hrefs, hex, hnd, horig⟩ := key
    refine ⟨hf, hi, more, hfns, hrefs, hex, hnd, fun f hf' => ?_⟩
    obtain ⟨h1, g, hg, hn⟩ := horig f hf'
    exact ⟨iface, by rw [h1]; exact hiface, g, hg, hn⟩
  clear hiface htarget hself
  induction names generalizing s₁ with
  | nil =>
    simp only [List.forM, pure_ok] at hloop
    obtain ⟨-, rfl⟩ := hloop
    exact ⟨rfl, rfl, [], by simp, by simp, by simp, id, by simp⟩
  | cons n ns ih =>
    simp only [List.forM, bind_ok] at hloop
    obtain ⟨u₁, s₄, hstep, hloop⟩ := hloop
    simp only [ite_state] at hstep
    obtain ⟨u₂, s₅, htop, hstep⟩ := hstep
    obtain ⟨rfl, hfresh⟩ := declareTopLevel_ok htop
    split at hstep
    · -- A type alias or an interface: the functions do not change.
      rename_i htype
      cases hfa : iface.aliases.find? (·.name == n.name) with
      | some info =>
        simp only [hfa, modify_ok] at hstep
        subst hstep
        obtain ⟨hf, hi, more, hfns, hrefs, hex, hnd, horig⟩ := ih _ hloop
        exact ⟨hf, hi, more, hfns, fun f hf' => import_refs_cons (hrefs f hf'), hex, hnd, horig⟩
      | none =>
      cases hfe : iface.enums.find? (fun e => e.name == n.name && e.exported) with
      | some info =>
        simp only [hfa, hfe, modify_ok] at hstep
        subst hstep
        obtain ⟨hf, hi, more, hfns, hrefs, hex, hnd, horig⟩ := ih _ hloop
        exact ⟨hf, hi, more, hfns, fun f hf' => import_refs_cons (hrefs f hf'), hex, hnd, horig⟩
      | none =>
      cases hfu : iface.unions.find? (fun u => u.name == n.name && u.exported) with
      | some info =>
        simp only [hfa, hfe, hfu, modify_ok] at hstep
        subst hstep
        obtain ⟨hf, hi, more, hfns, hrefs, hex, hnd, horig⟩ := ih _ hloop
        exact ⟨hf, hi, more, hfns, fun f hf' => import_refs_cons (hrefs f hf'), hex, hnd, horig⟩
      | none =>
        simp only [hfa, hfe, hfu, bind_ok, orReject_ok, modify_ok] at hstep
        obtain ⟨info, s₆, ⟨-, rfl⟩, rfl⟩ := hstep
        obtain ⟨hf, hi, more, hfns, hrefs, hex, hnd, horig⟩ := ih _ hloop
        exact ⟨hf, hi, more, hfns, fun f hf' => import_refs_cons (hrefs f hf'), hex, hnd, horig⟩
    · rename_i htype
      try simp only [ite_state] at hstep
      split at hstep
      · simp at hstep
      try simp only [pure_bind] at hstep
      cases hse : iface.stringEnum? n.name with
      | some p =>
        -- A string enum: the functions do not change.
        obtain ⟨info, pairs⟩ := p
        simp only [hse, modify_ok] at hstep
        subst hstep
        obtain ⟨hf, hi, more, hfns, hrefs, hex, hnd, horig⟩ := ih _ hloop
        exact ⟨hf, hi, more, hfns, fun f hf' => import_refs_cons (hrefs f hf'), hex, hnd, horig⟩
      | none =>
      simp only [hse] at hstep
      split at hstep
      · simp at hstep
      · simp only [bind_ok, orReject_ok, modify_ok] at hstep
        obtain ⟨fn, s₆, ⟨hfind, rfl⟩, rfl⟩ := hstep
        obtain ⟨hf, hi, more, hfns, hrefs, hex, hnd, horig⟩ := ih _ hloop
        have hname : fn.name = n.name := by simpa using List.find?_some hfind
        have hfile := hgf fn (List.mem_of_find?_eq_some hfind)
        refine ⟨hf, hi, { fn with exported := false } :: more, by simpa using hfns, ?_, ?_, ?_, ?_⟩
        · intro f hf'
          rcases List.mem_cons.mp hf' with rfl | hf'
          · simp [htype, FnInfo.ref, hname, hfile]
          · exact import_refs_cons (hrefs f hf')
        · intro f hf'
          rcases List.mem_cons.mp hf' with rfl | hf'
          · rfl
          · exact hex f hf'
        · intro hnd₀
          have := hnd (by
            simp only [List.map_append, List.map_cons, List.map_nil]
            rw [List.nodup_append]
            refine ⟨hnd₀, by simp, ?_⟩
            intro a ha b hb
            simp only [List.mem_singleton] at hb
            subst hb
            obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
            simpa [hname] using hfresh g hg)
          simpa using this
        · intro f hf'
          rcases List.mem_cons.mp hf' with rfl | hf'
          · exact ⟨hfile, fn, List.mem_of_find?_eq_some hfind, rfl⟩
          · exact horig f hf'

theorem translateEnum_ok {sp : Span} {ex : Bool} {name : String} {members : List String}
    {s s' : Ctx} {o : IR.Decl} (h : translateEnum sp ex name members s = .ok o s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧ s'.functions = s.functions ∧
      o = .enum name members := by
  unfold translateEnum at h
  cases hb : badMember members with
  | some r => simp [hb] at h
  | none =>
    simp only [hb, bind_ok, modify_ok, pure_ok] at h
    obtain ⟨_, _, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem declareUnion_ok {sp : Span} {ex : Bool} {name : String} {field : Option String}
    {members : List (String × Ty)} {s s' : Ctx} {o : IR.Decl}
    (h : declareUnion sp ex name field members s = .ok o s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧ s'.functions = s.functions ∧
      ∃ f ps, o = .tagged name f ps := by
  unfold declareUnion at h
  cases hb : badMember (members.map (·.1)) with
  | some r => simp [hb] at h
  | none =>
    simp only [hb, bind_ok, modify_ok, pure_ok] at h
    obtain ⟨_, _, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, _, _, rfl⟩

theorem translateUnion_ok {sp : Span} {ex : Bool} {name : String} {members : List StructInfo}
    {s s' : Ctx} {o : IR.Decl} (h : translateUnion sp ex name members s = .ok o s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧ s'.functions = s.functions ∧
      ∃ f ps, o = .tagged name f ps := by
  unfold translateUnion at h
  cases ht : tagFieldOf members with
  | none => simp [ht] at h
  | some p => simp only [ht] at h; exact declareUnion_ok h

theorem translatePrimitiveUnion_ok {sp : Span} {ex : Bool} {name : String} {members : List String}
    {s s' : Ctx} {o : IR.Decl} (h : translatePrimitiveUnion sp ex name members s = .ok o s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧ s'.functions = s.functions ∧
      ∃ f ps, o = .tagged name f ps := by
  unfold translatePrimitiveUnion at h
  simp only [ite_state] at h
  split at h
  · simp only [bind_ok, requireFeature_ok] at h
    obtain ⟨_, _, ⟨-, rfl⟩, h⟩ := h
    exact declareUnion_ok h
  · simp only [pure_bind] at h
    exact declareUnion_ok h

theorem translateRecord_ok {ex : Bool} {name : String} {key value : TypeExpr} {s s' : Ctx}
    {o : IR.Decl} (h : translateRecord ex name key value s = .ok o s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧ s'.functions = s.functions ∧
      ∃ n tps fs, o = .struct n tps fs := by
  unfold translateRecord at h
  simp only [bind_ok, get_ok, orReject_ok] at h
  obtain ⟨_, s₁, hk, _, _, ⟨rfl, rfl⟩, info, s₂, ⟨-, rfl⟩, ty, s₃, hty, h⟩ := h
  obtain ⟨rfl, -⟩ := isolated_ok hk
  obtain ⟨rfl, -⟩ := isolated_ok hty
  cases hm : info.members.find? leanReserved.contains with
  | some _ => simp [hm] at h
  | none =>
    simp only [hm, pure_bind, bind_ok, modify_ok, pure_ok] at h
    obtain ⟨_, _, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, _, _, _, rfl⟩

theorem translateAlias_ok {sp : Span} {ex : Bool} {name : String} {tps : List String} {type : TypeExpr}
    {s s' : Ctx} {o : IR.Decl} (h : translateAlias sp ex name tps type s = .ok o s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧ s'.functions = s.functions ∧
      ((∃ n tps t, o = .alias n tps t) ∨ (∃ n ms, o = .enum n ms) ∨ (∃ n f ps, o = .tagged n f ps) ∨
        ∃ n tps fs, o = .struct n tps fs) := by
  unfold translateAlias at h
  simp only [bind_ok] at h
  obtain ⟨name', s₁, hname, u, s₂, htop, h⟩ := h
  obtain ⟨rfl, rfl⟩ := checkName_ok hname
  obtain ⟨rfl, -⟩ := declareTopLevel_ok htop
  simp only [ite_state] at h
  split at h
  · simp at h
  simp only [pure_bind] at h
  cases hl : stringLiterals type with
  | some ms =>
    simp only [hl, bind_ok, pure_ok] at h
    obtain ⟨d, s₃, he, rfl, rfl⟩ := h
    obtain ⟨h1, h2, h3, rfl⟩ := translateEnum_ok he
    exact ⟨h1, h2, h3, .inr (.inl ⟨_, _, rfl⟩)⟩
  | none =>
    simp only [hl, bind_ok, get_ok] at h
    obtain ⟨c, s₄, ⟨hc, hc4⟩, h⟩ := h
    cases hu : unionMembers c.structs type with
    | some ms =>
      simp only [hu, bind_ok, pure_ok] at h
      obtain ⟨d, s₅, hd, rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, f, ps, rfl⟩ := translateUnion_ok hd
      subst_vars
      exact ⟨h1, h2, h3, .inr (.inr (.inl ⟨_, _, _, rfl⟩))⟩
    | none =>
    cases hp : primitiveMembers type with
    | some ms =>
      simp only [hu, hp, bind_ok, pure_ok] at h
      obtain ⟨d, s₅, hd, rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, f, ps, rfl⟩ := translatePrimitiveUnion_ok hd
      subst_vars
      exact ⟨h1, h2, h3, .inr (.inr (.inl ⟨_, _, _, rfl⟩))⟩
    | none =>
    cases hr : recordArgs type with
    | some kv =>
      simp only [hu, hp, hr, bind_ok, pure_ok] at h
      obtain ⟨d, s₅, hd, rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, n, tps', fs, rfl⟩ := translateRecord_ok hd
      subst_vars
      exact ⟨h1, h2, h3, .inr (.inr (.inr ⟨_, _, _, rfl⟩))⟩
    | none =>
      simp only [hu, hp, hr, bind_ok, modify_ok, pure_ok] at h
      obtain ⟨_, s₅, hcheck, _, s₅', rfl, ty, s₆, hty, _, s₇, rfl, rfl, rfl⟩ := h
      obtain rfl := checkTypeParams_ok hcheck
      obtain ⟨rfl, -⟩ := isolated_ok hty
      subst_vars
      exact ⟨rfl, rfl, rfl, .inl ⟨_, _, _, rfl⟩⟩

theorem translateInterface_ok {sp : Span} {ex : Bool} {name : String} {tps : List String} {fields : List Field}
    {s s' : Ctx} {o : IR.Decl} (h : translateInterface sp ex name tps fields s = .ok o s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧ s'.functions = s.functions ∧
      ∃ n tps fs, o = .struct n tps fs := by
  unfold translateInterface at h
  simp only [bind_ok, modify_ok, pure_ok] at h
  obtain ⟨name', s₁, hname, u, s₂, htop, _, s₂', hcheck, _, s₂'', rfl, infos, s₃, hinfos, _, s₄, rfl, rfl, rfl⟩ := h
  obtain ⟨rfl, rfl⟩ := checkName_ok hname
  obtain ⟨rfl, -⟩ := declareTopLevel_ok htop
  obtain rfl := checkTypeParams_ok hcheck
  obtain ⟨rfl, -⟩ := isolated_ok hinfos
  exact ⟨rfl, rfl, rfl, _, _, _, rfl⟩

/-! ### The names a file declares, and its string enums -/

/-- What `taken` gives after the lists of the state grow. -/
theorem taken_of_lists {s s' : Ctx} {a : List StructInfo} {b : List AliasInfo} {c : List EnumInfo}
    {d : List UnionInfo} {e : List FnInfo}
    (h1 : s'.structs = s.structs ++ a) (h2 : s'.aliases = s.aliases ++ b) (h3 : s'.enums = s.enums ++ c)
    (h4 : s'.unions = s.unions ++ d) (h5 : s'.functions = s.functions ++ e) (x : String) :
    s'.taken x = (s.taken x || a.any (·.name == x) || b.any (·.name == x) || c.any (·.name == x) ||
      d.any (·.name == x) || e.any (·.name == x)) := by
  simp only [Ctx.taken, h1, h2, h3, h4, h5, List.any_append]
  cases s.structs.any (·.name == x) <;> cases s.aliases.any (·.name == x) <;>
    cases s.enums.any (·.name == x) <;> cases s.unions.any (·.name == x) <;>
    cases s.functions.any (·.name == x) <;> simp

/-- The string enum that an interface exports under a name. -/
theorem stringEnum_some {iface : Interface} {name : String} {info : EnumInfo}
    {pairs : List (String × String)} (h : iface.stringEnum? name = some (info, pairs)) :
    info ∈ iface.enums ∧ info.name = name ∧ info.exported = true ∧ info.named = some pairs := by
  unfold Interface.stringEnum? at h
  cases hf : iface.enums.find? (fun e => e.name == name && e.exported) with
  | none => simp [hf] at h
  | some i =>
    cases hn : i.named with
    | none => simp [hf, hn] at h
    | some ps =>
      simp only [hf, hn, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact ⟨List.mem_of_find?_eq_some hf, this.1, this.2, hn⟩

/-- The interfaces offer only string enums that the program's files export,
with the same members. -/
def FaithfulE (p : Eval.Program) (ifaces : List (String × Interface)) : Prop :=
  ∀ t i, ifaces.lookup t = some i → ∀ name info pairs, i.stringEnum? name = some (info, pairs) →
    ∃ tm, p.lookup t = some tm ∧ (Eval.enumsOf tm true).lookup name = some pairs

/-- What one declaration does to the names that the file declares and to its
string enums, in the program `P`: the names that the state declared stay
declared, the declaration binds names that were not declared and declares
them, each enum value that it adds is what it binds the enum's name to, and
each exported string enum that it adds is an exported `enum` of the file. -/
structure DeclNames (P : Eval.Program) (d : Decl) (s s' : Ctx) : Prop where
  file : s'.file = s.file
  mono : ∀ x, s.taken x = true → s'.taken x = true
  bound : ∀ x ∈ boundNames d, s'.taken x = true
  nodup : (boundNames d).Nodup
  fresh : ∀ x ∈ boundNames d, s.taken x = false
  values : ∃ more, s'.enumValues = s.enumValues ++ more ∧
    ∀ e ∈ more, Eval.enumBinding P s.file e.name d = some (some e.members)
  exports : ∃ more, s'.enums = s.enums ++ more ∧ ∀ i ∈ more, i.exported = true → ∀ pairs, i.named = some pairs →
    ∃ sp ms, d = .enum sp true i.name ms ∧ ms.map (fun x => (x.name, x.value)) = pairs

/-- The same for a list of declarations. -/
structure DeclsNames (P : Eval.Program) (ds : List Decl) (s s' : Ctx) : Prop where
  file : s'.file = s.file
  mono : ∀ x, s.taken x = true → s'.taken x = true
  bound : ∀ x ∈ ds.flatMap boundNames, s'.taken x = true
  nodup : (ds.flatMap boundNames).Nodup
  fresh : ∀ x ∈ ds.flatMap boundNames, s.taken x = false
  values : ∃ more, s'.enumValues = s.enumValues ++ more ∧
    ∀ e ∈ more, ∃ d ∈ ds, Eval.enumBinding P s.file e.name d = some (some e.members)
  exports : ∃ more, s'.enums = s.enums ++ more ∧ ∀ i ∈ more, i.exported = true → ∀ pairs, i.named = some pairs →
    ∃ sp ms, Decl.enum sp true i.name ms ∈ ds ∧ ms.map (fun x => (x.name, x.value)) = pairs

theorem DeclsNames.nil (P : Eval.Program) (s : Ctx) : DeclsNames P [] s s :=
  ⟨rfl, fun _ h => h, by simp, by simp, by simp, ⟨[], by simp, by simp⟩, ⟨[], by simp, by simp⟩⟩

theorem DeclsNames.cons {P : Eval.Program} {d : Decl} {ds : List Decl} {s s₁ s₂ : Ctx}
    (h₁ : DeclNames P d s s₁) (h₂ : DeclsNames P ds s₁ s₂) : DeclsNames P (d :: ds) s s₂ where
  file := h₂.file.trans h₁.file
  mono x hx := h₂.mono x (h₁.mono x hx)
  bound x hx := by
    rw [List.flatMap_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · exact h₂.mono x (h₁.bound x hx)
    · exact h₂.bound x hx
  nodup := by
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨h₁.nodup, h₂.nodup, fun a ha b hb hab => ?_⟩
    subst hab
    have := h₂.fresh a hb
    rw [h₁.bound a ha] at this
    cases this
  fresh x hx := by
    rw [List.flatMap_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · exact h₁.fresh x hx
    · cases h : s.taken x
      · rfl
      · have := h₂.fresh x hx
        rw [h₁.mono x h] at this
        cases this
  values := by
    obtain ⟨m₁, e₁, hv₁⟩ := h₁.values
    obtain ⟨m₂, e₂, hv₂⟩ := h₂.values
    refine ⟨m₁ ++ m₂, by rw [e₂, e₁, List.append_assoc], fun e he => ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact ⟨d, List.mem_cons_self .., hv₁ e he⟩
    · obtain ⟨d', hd', hb⟩ := hv₂ e he
      exact ⟨d', List.mem_cons_of_mem _ hd', by rw [← h₁.file]; exact hb⟩
  exports := by
    obtain ⟨m₁, e₁, hx₁⟩ := h₁.exports
    obtain ⟨m₂, e₂, hx₂⟩ := h₂.exports
    refine ⟨m₁ ++ m₂, by rw [e₂, e₁, List.append_assoc], fun i hi hex pairs hn => ?_⟩
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨sp, ms, hd, hms⟩ := hx₁ i hi hex pairs hn
      exact ⟨sp, ms, by rw [← hd]; exact List.mem_cons_self .., hms⟩
    · obtain ⟨sp, ms, hd, hms⟩ := hx₂ i hi hex pairs hn
      exact ⟨sp, ms, List.mem_cons_of_mem _ hd, hms⟩

/-- An interface adds one structure with its name. -/
theorem translateInterface_shape {sp : Span} {ex : Bool} {name : String} {tps : List String}
    {fields : List Field} {s s' : Ctx} {o : IR.Decl} (h : translateInterface sp ex name tps fields s = .ok o s') :
    s.taken name = false ∧ ∃ i : StructInfo, i.name = name ∧
      s' = { s with typeParams := [], structs := s.structs ++ [i] } := by
  unfold translateInterface at h
  simp only [bind_ok, modify_ok, pure_ok] at h
  obtain ⟨name', s₁, hname, u, s₂, htop, _, s₂', hcheck, _, s₂'', rfl, infos, s₃, hinfos, _, s₄, rfl, rfl, rfl⟩ := h
  obtain ⟨rfl, rfl⟩ := checkName_ok hname
  have hfresh := declareTopLevel_fresh htop
  obtain ⟨rfl, -⟩ := declareTopLevel_ok htop
  obtain rfl := checkTypeParams_ok hcheck
  obtain ⟨rfl, -⟩ := isolated_ok hinfos
  exact ⟨hfresh, _, rfl, rfl⟩

/-- `Record<K, V>` adds one structure with its name, as an interface does. -/
theorem translateRecord_shape {ex : Bool} {name : String} {key value : TypeExpr} {s s' : Ctx}
    {o : IR.Decl} (h : translateRecord ex name key value s = .ok o s') :
    ∃ i : StructInfo, i.name = name ∧ s' = { s with structs := s.structs ++ [i] } := by
  unfold translateRecord at h
  simp only [bind_ok, get_ok, orReject_ok] at h
  obtain ⟨_, s₁, hk, _, _, ⟨rfl, rfl⟩, info, s₂, ⟨-, rfl⟩, ty, s₃, hty, h⟩ := h
  obtain ⟨rfl, -⟩ := isolated_ok hk
  obtain ⟨rfl, -⟩ := isolated_ok hty
  cases hm : info.members.find? leanReserved.contains with
  | some _ => simp [hm] at h
  | none =>
    simp only [hm, pure_bind, bind_ok, modify_ok, pure_ok] at h
    obtain ⟨_, _, rfl, rfl, rfl⟩ := h
    exact ⟨_, rfl, rfl⟩

/-- An interface: it declares its name in the structures. -/
theorem translateInterface_names {P : Eval.Program} {sp : Span} {ex : Bool} {name : String} {tps : List String}
    {fields : List Field} {s s' : Ctx} {o : IR.Decl} (h : translateInterface sp ex name tps fields s = .ok o s') :
    DeclNames P (.interface sp ex name tps fields) s s' := by
  obtain ⟨hfresh, i, hi, rfl⟩ := translateInterface_shape h
  have ht := taken_of_lists (s := s) (s' := { s with typeParams := [], structs := s.structs ++ [i] }) (b := []) (c := [])
    (d := []) (e := []) rfl (by simp) (by simp) (by simp) (by simp)
  refine ⟨rfl, fun x hx => by simp [ht, hx], fun x hx => ?_, by simp [boundNames], fun x hx => ?_,
    ⟨[], by simp, by simp⟩, ⟨[], by simp, by simp⟩⟩
  · simp only [boundNames, List.mem_singleton] at hx; subst hx; simp [ht, hi]
  · simp only [boundNames, List.mem_singleton] at hx; subst hx; exact hfresh

/-- A function: it declares its name in the functions. -/
theorem translateFunction_names {P : Eval.Program} {thr : String → Bool}
    {cls : String → Option (Option (List CtorParam × Expr))} {classes : List ClassInfo} {sp : Span} {ex : Bool}
    {name : String} {tps : List String} {params : List Param} {ret : Option TypeExpr} {body : Stmt} {s s' : Ctx}
    {o : IR.Decl} (h : translateFunction thr cls classes sp ex name tps params ret body s = .ok o s') :
    DeclNames P (.function sp ex name tps params ret body) s s' := by
  obtain ⟨hl, hfresh, hf, -, -, f, hfns, -, hname, -⟩ := translateFunction_ok h
  simp only [Prod.mk.injEq] at hl
  obtain ⟨h1, h2, h3, h4, h5⟩ := hl
  have ht := taken_of_lists (a := []) (b := []) (c := []) (d := []) (by simp [h1]) (by simp [h2])
    (by simp [h3]) (by simp [h4]) hfns
  refine ⟨hf, fun x hx => by simp [ht, hx], fun x hx => ?_, by simp [boundNames], fun x hx => ?_,
    ⟨[], by simp [h5], by simp⟩, ⟨[], by simp [h3], by simp⟩⟩
  · simp only [boundNames, List.mem_singleton] at hx; subst hx; simp [ht, hname]
  · simp only [boundNames, List.mem_singleton] at hx; subst hx; exact hfresh

/-- `enum T { … }` adds one literal union and one enum value, both with its
name and its members. -/
theorem translateStringEnum_shape {sp : Span} {ex : Bool} {name : String} {members : List EnumMember}
    {s s' : Ctx} {o : IR.Decl} (h : translateStringEnum sp ex name members s = .ok o s') :
    s.taken name = false ∧ o = .enum name (members.map (·.value)) ∧
      ∃ (i : EnumInfo) (v : EnumValue), i.name = name ∧ i.exported = ex ∧
        i.named = some (members.map fun m => (m.name, m.value)) ∧ v.name = name ∧
        v.members = members.map (fun m => (m.name, m.value)) ∧
        s' = { s with enums := s.enums ++ [i], enumValues := s.enumValues ++ [v] } := by
  unfold translateStringEnum at h
  simp only [bind_ok] at h
  obtain ⟨name', s₁, hname, u, s₂, htop, h⟩ := h
  obtain ⟨rfl, rfl⟩ := checkName_ok hname
  have hfresh := declareTopLevel_fresh htop
  obtain ⟨rfl, -⟩ := declareTopLevel_ok htop
  cases hr : enumRefusal sp members with
  | some r => obtain ⟨sp', reason⟩ := r; simp [hr] at h
  | none =>
    simp only [hr, bind_ok, modify_ok, pure_ok] at h
    obtain ⟨_, _, rfl, rfl, rfl⟩ := h
    exact ⟨hfresh, by simp, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `enum T { … }`: it declares its name in the literal unions, and it is the
value of its name. -/
theorem translateStringEnum_names {P : Eval.Program} {sp : Span} {ex : Bool} {name : String}
    {members : List EnumMember} {s s' : Ctx} {o : IR.Decl} (h : translateStringEnum sp ex name members s = .ok o s') :
    DeclNames P (.enum sp ex name members) s s' := by
  obtain ⟨hfresh, -, i, v, hin, hie, hinamed, hvn, hvm, rfl⟩ := translateStringEnum_shape h
  have ht := taken_of_lists (s := s) (s' := { s with enums := s.enums ++ [i], enumValues := s.enumValues ++ [v] })
    (a := []) (b := []) (d := []) (e := []) (by simp) (by simp) rfl (by simp) (by simp)
  refine ⟨rfl, fun x hx => by simp [ht, hx], fun x hx => ?_, by simp [boundNames], fun x hx => ?_,
    ⟨[v], rfl, fun e he => ?_⟩, ⟨[i], rfl, fun i' hi' hex ps hn => ?_⟩⟩
  · simp only [boundNames, List.mem_singleton] at hx; subst hx; simp [ht, hin]
  · simp only [boundNames, List.mem_singleton] at hx; subst hx; exact hfresh
  · simp only [List.mem_singleton] at he; subst he; simp [Eval.enumBinding, hvn, hvm]
  · simp only [List.mem_singleton] at hi'; subst hi'
    rw [hinamed, Option.some.injEq] at hn
    rw [hie] at hex
    subst hex
    exact ⟨sp, members, by rw [hin], hn⟩

/-- A step that grows the lists of the state keeps every name declared, and
declares a name that one of the new entries has. -/
theorem taken_grow {s s' : Ctx} {name : String} {a : List StructInfo} {b : List AliasInfo}
    {c : List EnumInfo} {d : List UnionInfo} {e : List FnInfo}
    (h1 : s'.structs = s.structs ++ a) (h2 : s'.aliases = s.aliases ++ b) (h3 : s'.enums = s.enums ++ c)
    (h4 : s'.unions = s.unions ++ d) (h5 : s'.functions = s.functions ++ e)
    (hname : (a.any (·.name == name) || b.any (·.name == name) || c.any (·.name == name) ||
      d.any (·.name == name) || e.any (·.name == name)) = true) :
    (∀ x, s.taken x = true → s'.taken x = true) ∧ s'.taken name = true := by
  have ht := taken_of_lists h1 h2 h3 h4 h5
  refine ⟨fun x hx => by simp [ht, hx], ?_⟩
  rw [ht]
  simp only [Bool.or_assoc] at hname ⊢
  rw [hname, Bool.or_true]

/-- A declaration that binds one name, declares it in one of the lists of the
state, and adds no enum value and no string enum. -/
theorem DeclNames.one {P : Eval.Program} {d : Decl} {s s' : Ctx} {name : String}
    (hb : boundNames d = [name]) (hfresh : s.taken name = false) (hfile : s'.file = s.file)
    {a : List StructInfo} {b : List AliasInfo} {c : List EnumInfo} {dd : List UnionInfo} {e : List FnInfo}
    (h1 : s'.structs = s.structs ++ a) (h2 : s'.aliases = s.aliases ++ b) (h3 : s'.enums = s.enums ++ c)
    (h4 : s'.unions = s.unions ++ dd) (h5 : s'.functions = s.functions ++ e) (h6 : s'.enumValues = s.enumValues)
    (hnamed : ∀ i ∈ c, i.named = none)
    (hname : (a.any (·.name == name) || b.any (·.name == name) || c.any (·.name == name) ||
      dd.any (·.name == name) || e.any (·.name == name)) = true) :
    DeclNames P d s s' := by
  have ht := taken_of_lists h1 h2 h3 h4 h5
  refine ⟨hfile, fun x hx => by simp [ht, hx], fun x hx => ?_, by simp [hb], fun x hx => ?_,
    ⟨[], by simp [h6], by simp⟩, ⟨c, h3, fun i hi _ ps hn => by rw [hnamed i hi] at hn; cases hn⟩⟩
  · rw [hb, List.mem_singleton] at hx
    subst hx
    rw [ht]
    simp only [Bool.or_assoc] at hname ⊢
    rw [hname, Bool.or_true]
  · rw [hb, List.mem_singleton] at hx
    subst hx
    exact hfresh

theorem translateEnum_shape {sp : Span} {ex : Bool} {name : String} {members : List String}
    {s s' : Ctx} {o : IR.Decl} (h : translateEnum sp ex name members s = .ok o s') :
    ∃ i : EnumInfo, i.name = name ∧ i.named = none ∧ s' = { s with enums := s.enums ++ [i] } := by
  unfold translateEnum at h
  cases hb : badMember members with
  | some r => simp [hb] at h
  | none =>
    simp only [hb, bind_ok, modify_ok, pure_ok] at h
    obtain ⟨_, _, rfl, rfl, rfl⟩ := h
    exact ⟨_, rfl, rfl, rfl⟩

theorem declareUnion_shape {sp : Span} {ex : Bool} {name : String} {field : Option String}
    {members : List (String × Ty)} {s s' : Ctx} {o : IR.Decl}
    (h : declareUnion sp ex name field members s = .ok o s') :
    ∃ u : UnionInfo, u.name = name ∧ s' = { s with unions := s.unions ++ [u] } := by
  unfold declareUnion at h
  cases hb : badMember (members.map (·.1)) with
  | some r => simp [hb] at h
  | none =>
    simp only [hb, bind_ok, modify_ok, pure_ok] at h
    obtain ⟨_, _, rfl, rfl, rfl⟩ := h
    exact ⟨_, rfl, rfl⟩

theorem translateUnion_shape {sp : Span} {ex : Bool} {name : String} {members : List StructInfo}
    {s s' : Ctx} {o : IR.Decl} (h : translateUnion sp ex name members s = .ok o s') :
    ∃ u : UnionInfo, u.name = name ∧ s' = { s with unions := s.unions ++ [u] } := by
  unfold translateUnion at h
  cases ht : tagFieldOf members with
  | none => simp [ht] at h
  | some p => simp only [ht] at h; exact declareUnion_shape h

theorem translatePrimitiveUnion_shape {sp : Span} {ex : Bool} {name : String} {members : List String}
    {s s' : Ctx} {o : IR.Decl} (h : translatePrimitiveUnion sp ex name members s = .ok o s') :
    ∃ u : UnionInfo, u.name = name ∧ s' = { s with unions := s.unions ++ [u] } := by
  unfold translatePrimitiveUnion at h
  simp only [ite_state] at h
  split at h
  · simp only [bind_ok, requireFeature_ok] at h
    obtain ⟨_, _, ⟨-, rfl⟩, h⟩ := h
    exact declareUnion_shape h
  · simp only [pure_bind] at h
    exact declareUnion_shape h

/-- A type alias: it declares its name in the aliases, the literal unions or
the tagged unions. -/
theorem translateAlias_names {P : Eval.Program} {sp : Span} {ex : Bool} {name : String} {tps : List String}
    {type : TypeExpr} {s s' : Ctx} {o : IR.Decl} (h : translateAlias sp ex name tps type s = .ok o s') :
    DeclNames P (.typeAlias sp ex name tps type) s s' := by
  unfold translateAlias at h
  simp only [bind_ok] at h
  obtain ⟨name', s₁, hname, u, s₂, htop, h⟩ := h
  obtain ⟨rfl, rfl⟩ := checkName_ok hname
  have hfresh := declareTopLevel_fresh htop
  obtain ⟨rfl, -⟩ := declareTopLevel_ok htop
  simp only [ite_state] at h
  split at h
  · simp at h
  simp only [pure_bind] at h
  cases hl : stringLiterals type with
  | some ms =>
    simp only [hl, bind_ok, pure_ok] at h
    obtain ⟨d, s₃, he, rfl, rfl⟩ := h
    obtain ⟨i, hi, hin, rfl⟩ := translateEnum_shape he
    exact DeclNames.one rfl hfresh rfl (a := []) (b := []) (dd := []) (e := []) (by simp) (by simp) rfl
      (by simp) (by simp) rfl (by simp [hin]) (by simp [hi])
  | none =>
    simp only [hl, bind_ok, get_ok] at h
    obtain ⟨c, s₄, ⟨hc, hc4⟩, h⟩ := h
    cases hu : unionMembers c.structs type with
    | some ms =>
      simp only [hu, bind_ok, pure_ok] at h
      obtain ⟨d, s₅, hd, rfl, rfl⟩ := h
      obtain ⟨u', hu', rfl⟩ := translateUnion_shape hd
      subst_vars
      exact DeclNames.one rfl hfresh rfl (a := []) (b := []) (c := []) (e := []) (by simp) (by simp) (by simp)
        rfl (by simp) rfl (by simp) (by simp)
    | none =>
    cases hp : primitiveMembers type with
    | some ms =>
      simp only [hu, hp, bind_ok, pure_ok] at h
      obtain ⟨d, s₅, hd, rfl, rfl⟩ := h
      obtain ⟨u', hu', rfl⟩ := translatePrimitiveUnion_shape hd
      subst_vars
      exact DeclNames.one rfl hfresh rfl (a := []) (b := []) (c := []) (e := []) (by simp) (by simp) (by simp)
        rfl (by simp) rfl (by simp) (by simp)
    | none =>
    cases hr : recordArgs type with
    | some kv =>
      simp only [hu, hp, hr, bind_ok, pure_ok] at h
      obtain ⟨d, s₅, hd, rfl, rfl⟩ := h
      obtain ⟨i, hi, rfl⟩ := translateRecord_shape hd
      subst_vars
      exact DeclNames.one rfl hfresh rfl (b := []) (c := []) (dd := []) (e := []) rfl (by simp) (by simp)
        (by simp) (by simp) rfl (by simp) (by simp)
    | none =>
      simp only [hu, hp, hr, bind_ok, modify_ok, pure_ok] at h
      obtain ⟨_, s₅, hcheck, _, s₅', rfl, ty, s₆, hty, _, s₇, rfl, rfl, rfl⟩ := h
      obtain rfl := checkTypeParams_ok hcheck
      obtain ⟨rfl, -⟩ := isolated_ok hty
      subst_vars
      exact DeclNames.one rfl hfresh rfl (a := []) (c := []) (dd := []) (e := []) (by simp) rfl (by simp)
        (by simp) (by simp) rfl (by simp) (by simp)

/-- An import that names one more name binds what the shorter import binds. -/
theorem enumBinding_import_cons {P : Eval.Program} {file x source : String} {sp : Span} {n : ImportName}
    {ns : List ImportName} {v : Option (List (String × String))}
    (h : Eval.enumBinding P file x (.import sp ns source) = some v) :
    Eval.enumBinding P file x (.import sp (n :: ns) source) = some v := by
  simp only [Eval.enumBinding] at h ⊢
  split at h
  · rename_i hany
    rw [if_pos (by simp only [List.any_cons, hany, Bool.or_true])]
    exact h
  · simp at h

/-- One more name of an import: it was not declared, and it is declared after. -/
theorem importNames_cons {P : Eval.Program} {sp : Span} {n : ImportName} {ns : List ImportName}
    {source : String} {s s₄ s' : Ctx} (hfresh : s.taken n.name = false)
    (hmono : ∀ x, s.taken x = true → s₄.taken x = true) (hbound : s₄.taken n.name = true)
    (hfile : s₄.file = s.file)
    (hv : ∃ more, s₄.enumValues = s.enumValues ++ more ∧
      ∀ e ∈ more, Eval.enumBinding P s.file e.name (.import sp (n :: ns) source) = some (some e.members))
    (hx : ∃ more, s₄.enums = s.enums ++ more ∧ ∀ i ∈ more, i.exported = false)
    (ih : DeclNames P (.import sp ns source) s₄ s') : DeclNames P (.import sp (n :: ns) source) s s' where
  file := ih.file.trans hfile
  mono x hx := ih.mono x (hmono x hx)
  bound x hx := by
    simp only [boundNames, List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ih.mono _ hbound
    · exact ih.bound x hx
  nodup := by
    simp only [boundNames, List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih.nodup⟩
    have := ih.fresh _ hm
    rw [hbound] at this
    cases this
  fresh x hx := by
    simp only [boundNames, List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hfresh
    · cases h : s.taken x
      · rfl
      · have := ih.fresh x hx
        rw [hmono x h] at this
        cases this
  values := by
    obtain ⟨m₁, e₁, hv₁⟩ := hv
    obtain ⟨m₂, e₂, hv₂⟩ := ih.values
    refine ⟨m₁ ++ m₂, by rw [e₂, e₁, List.append_assoc], fun e he => ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact hv₁ e he
    · have := hv₂ e he
      rw [hfile] at this
      exact enumBinding_import_cons this
  exports := by
    obtain ⟨m₁, e₁, hx₁⟩ := hx
    obtain ⟨m₂, e₂, hx₂⟩ := ih.exports
    refine ⟨m₁ ++ m₂, by rw [e₂, e₁, List.append_assoc], fun i hi hex pairs hn => ?_⟩
    rcases List.mem_append.mp hi with hi | hi
    · rw [hx₁ i hi] at hex; cases hex
    · obtain ⟨_, _, hd, _⟩ := hx₂ i hi hex pairs hn
      cases hd

/-- An import: it declares each name that it names, and a string enum that it
imports without `type` is the value of its name. -/
theorem translateImport_names {P : Eval.Program} {sp : Span} {names : List ImportName} {source : String}
    {s s' : Ctx} {u : Unit} (hfe : FaithfulE P s.interfaces) (h : translateImport sp names source s = .ok u s') :
    DeclNames P (.import sp names source) s s' := by
  unfold translateImport at h
  simp only [bind_ok, get_ok, orReject_ok] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, target, s₂, ⟨htarget, rfl⟩, iface, s₃, ⟨hiface, rfl⟩, hloop⟩ := h
  simp only [ite_state] at hloop
  split at hloop
  · simp at hloop
  rename_i hyear
  clear hyear
  simp only [pure_bind] at hloop
  induction names generalizing s₁ with
  | nil =>
    simp only [List.forM, pure_ok] at hloop
    obtain ⟨-, rfl⟩ := hloop
    exact ⟨rfl, fun _ h => h, by simp [boundNames], by simp [boundNames], by simp [boundNames],
      ⟨[], by simp, by simp⟩, ⟨[], by simp, by simp⟩⟩
  | cons n ns ih =>
    simp only [List.forM, bind_ok] at hloop
    obtain ⟨u₁, s₄, hstep, hloop⟩ := hloop
    simp only [ite_state] at hstep
    obtain ⟨u₂, s₅, htop, hstep⟩ := hstep
    have hfresh := declareTopLevel_fresh htop
    obtain ⟨rfl, -⟩ := declareTopLevel_ok htop
    split at hstep
    · -- A type: the functions and the enum values do not change.
      rename_i htype
      cases hfa : iface.aliases.find? (·.name == n.name) with
      | some info =>
        simp only [hfa, modify_ok] at hstep
        subst hstep
        have hn : info.name = n.name := by simpa using List.find?_some hfa
        have hrest := ih _ (by exact hfe) (by exact htarget) (by exact hiface) hloop
        refine importNames_cons hfresh ?_ ?_ (by rfl) ⟨[], by simp, by simp⟩ ⟨[], by simp, by simp⟩ hrest
        · exact (taken_grow (name := n.name) (a := []) (c := []) (d := []) (e := []) (by simp) rfl (by simp) (by simp) (by simp) (by simp [hn])).1
        · exact (taken_grow (name := n.name) (a := []) (c := []) (d := []) (e := []) (by simp) rfl (by simp) (by simp) (by simp) (by simp [hn])).2
      | none =>
      cases hfe' : iface.enums.find? (fun e => e.name == n.name && e.exported) with
      | some info =>
        simp only [hfa, hfe', modify_ok] at hstep
        subst hstep
        have hn : info.name = n.name := by have := List.find?_some hfe'; simp at this; exact this.1
        have hrest := ih _ (by exact hfe) (by exact htarget) (by exact hiface) hloop
        refine importNames_cons hfresh ?_ ?_ (by rfl) ⟨[], by simp, by simp⟩ ⟨_, rfl, by simp⟩ hrest
        · exact (taken_grow (name := n.name) (a := []) (b := []) (d := []) (e := []) (by simp) (by simp) rfl (by simp) (by simp) (by simp [hn])).1
        · exact (taken_grow (name := n.name) (a := []) (b := []) (d := []) (e := []) (by simp) (by simp) rfl (by simp) (by simp) (by simp [hn])).2
      | none =>
      cases hfu : iface.unions.find? (fun u => u.name == n.name && u.exported) with
      | some info =>
        simp only [hfa, hfe', hfu, modify_ok] at hstep
        subst hstep
        have hn : info.name = n.name := by have := List.find?_some hfu; simp at this; exact this.1
        have hrest := ih _ (by exact hfe) (by exact htarget) (by exact hiface) hloop
        refine importNames_cons hfresh ?_ ?_ (by rfl) ⟨[], by simp, by simp⟩ ⟨[], by simp, by simp⟩ hrest
        · exact (taken_grow (name := n.name) (a := []) (b := []) (c := []) (e := []) (by simp) (by simp) (by simp) rfl (by simp) (by simp [hn])).1
        · exact (taken_grow (name := n.name) (a := []) (b := []) (c := []) (e := []) (by simp) (by simp) (by simp) rfl (by simp) (by simp [hn])).2
      | none =>
        simp only [hfa, hfe', hfu, bind_ok, orReject_ok, modify_ok] at hstep
        obtain ⟨info, s₆, ⟨hfs, rfl⟩, rfl⟩ := hstep
        have hn : info.name = n.name := by have := List.find?_some hfs; simp at this; exact this.1
        have hrest := ih _ (by exact hfe) (by exact htarget) (by exact hiface) hloop
        refine importNames_cons hfresh ?_ ?_ (by rfl) ⟨[], by simp, by simp⟩ ⟨[], by simp, by simp⟩ hrest
        · exact (taken_grow (name := n.name) (b := []) (c := []) (d := []) (e := []) rfl (by simp) (by simp) (by simp) (by simp) (by simp [hn])).1
        · exact (taken_grow (name := n.name) (b := []) (c := []) (d := []) (e := []) rfl (by simp) (by simp) (by simp) (by simp) (by simp [hn])).2
    · rename_i htype
      try simp only [ite_state] at hstep
      split at hstep
      · simp at hstep
      try simp only [pure_bind] at hstep
      cases hse : iface.stringEnum? n.name with
      | some p =>
        -- A string enum: its value is the enum that the file exports.
        obtain ⟨info, pairs⟩ := p
        simp only [hse, modify_ok] at hstep
        subst hstep
        obtain ⟨-, hn, -, -⟩ := stringEnum_some hse
        obtain ⟨tm, htm, hl⟩ := hfe target iface hiface n.name info pairs hse
        have hrest := ih _ (by exact hfe) (by exact htarget) (by exact hiface) hloop
        refine importNames_cons hfresh ?_ ?_ (by rfl) ⟨_, rfl, fun e he => ?_⟩ ⟨_, rfl, by simp⟩ hrest
        · exact (taken_grow (name := n.name) (a := []) (b := []) (d := []) (e := []) (by simp) (by simp) rfl (by simp) (by simp) (by simp [hn])).1
        · exact (taken_grow (name := n.name) (a := []) (b := []) (d := []) (e := []) (by simp) (by simp) rfl (by simp) (by simp) (by simp [hn])).2
        simp only [List.mem_singleton] at he
        subst he
        have hnt : n.typeOnly = false := by simpa using htype
        simp [Eval.enumBinding, hnt, htarget, htm, hl]
      | none =>
      simp only [hse] at hstep
      split at hstep
      · simp at hstep
      · simp only [bind_ok, orReject_ok, modify_ok] at hstep
        obtain ⟨fn, s₆, ⟨hfind, rfl⟩, rfl⟩ := hstep
        have hn : fn.name = n.name := by simpa using List.find?_some hfind
        have hrest := ih _ (by exact hfe) (by exact htarget) (by exact hiface) hloop
        refine importNames_cons hfresh ?_ ?_ (by rfl) ⟨[], by simp, by simp⟩ ⟨[], by simp, by simp⟩ hrest
        · exact (taken_grow (name := n.name) (a := []) (b := []) (c := []) (d := []) (by simp) (by simp) (by simp)
            (by simp) rfl (by simp [hn])).1
        · exact (taken_grow (name := n.name) (a := []) (b := []) (c := []) (d := []) (by simp) (by simp) (by simp)
            (by simp) rfl (by simp [hn])).2

/-- An export list only checks the state: it adds no declaration and keeps the
state. -/
theorem translateExports_ok {thr : String → Bool} {cls : String → Option (Option (List CtorParam × Expr))}
    {classes : List ClassInfo} {sp : Span} {names : List ImportName} {source : Option String} {s s' : Ctx}
    {o : Option IR.Decl} (h : translateDecl thr cls classes (.exports sp names source) s = .ok o s') :
    o = none ∧ s' = s := by
  simp only [translateDecl] at h
  simp only [bind_ok] at h
  obtain ⟨c, s₁, hg, h⟩ := h
  simp only [get, getThe, MonadStateOf.get, EStateM.get, EStateM.Result.ok.injEq] at hg
  obtain ⟨rfl, rfl⟩ := hg
  cases he : exportListError? s sp names source with
  | some pm => simp [he] at h
  | none =>
    simp only [he, pure_bind, pure_ok] at h
    exact ⟨h.1.symm, h.2.symm⟩

/-- `translateDecls` translates the error classes and then each declaration,
after it checks that no name is in two export lists. -/
theorem translateDecls_ok {m : Module} {s s' : Ctx} {ds : List IR.Decl}
    (h : translateDecls m s = .ok ds s') :
    ∃ pre s₁ os, translateErrorTypes m s = .ok pre s₁ ∧
      m.decls.mapM (translateDecl (Eval.mayThrow m) (Eval.errorClassOf m) s₁.errorClasses) s₁ = .ok os s' ∧
      ds = pre ++ os.filterMap id := by
  simp only [translateDecls] at h
  cases hd : duplicateExport? m with
  | some n => simp [hd] at h
  | none =>
    simp only [hd, pure_bind, bind_ok, get_ok, pure_ok] at h
    obtain ⟨pre, s₁, hpre, _, _, ⟨rfl, rfl⟩, os, s₂, hos, rfl, rfl⟩ := h
    exact ⟨_, _, _, hpre, hos, rfl⟩

/-- Each parameter of a constructor translates to its name and its type,
with its `readonly` mark. -/
theorem translateCtorParam_ok {p : CtorParam} {s s' : Ctx} {x : String × Ty × Bool}
    (h : translateCtorParam p s = .ok x s') : x.1 = p.param.name ∧ x.2.2 = p.readonly := by
  unfold translateCtorParam at h
  simp only [ite_state] at h
  split at h
  · simp at h
  · simp only [pure_bind, bind_ok, orReject_ok] at h
    obtain ⟨type, s₁, ⟨-, rfl⟩, pn, s₂, hpn, h⟩ := h
    obtain ⟨rfl, -⟩ := checkLocalName_ok hpn
    simp only [ite_state] at h
    split at h
    · simp at h
    · simp only [bind_ok] at h
      obtain ⟨ty, s₃, -, h⟩ := h
      cases ty <;> simp at h <;> obtain ⟨rfl, -⟩ := h <;> exact ⟨rfl, rfl⟩

/-- The parameters of an error class, as translated, are the parameters of
its constructor: the same names, with the same `readonly` marks. -/
theorem ctorParams_shape : ∀ (ps : List CtorParam) (s s' : Ctx) (params : List (String × Ty × Bool)),
    ps.mapM translateCtorParam s = .ok params s' →
    params.map (fun x => (x.1, x.2.2)) = ps.map fun p => (p.param.name, p.readonly)
  | [], _, _, _, h => by
    simp only [List.mapM_nil, pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | p :: ps, s, s', params, h => by
    simp only [List.mapM_cons, bind_ok, pure_ok] at h
    obtain ⟨x, s₁, hx, xs, s₂, hxs, rfl, -⟩ := h
    obtain ⟨h1, h2⟩ := translateCtorParam_ok hx
    simp [ctorParams_shape ps _ _ _ hxs, h1, h2]

/-- What an error class does to the state: it adds itself to the error
classes and changes nothing else. Its name is new among them and is not a
global's, and its parameters are the constructor's. -/
theorem translateErrorClass_ok {sp : Span} {ex : Bool} {name : String} {ctor : Option (List CtorParam × Expr)}
    {s s' : Ctx} {info : ClassInfo} (h : translateErrorClass sp ex name ctor s = .ok info s') :
    s' = { s with errorClasses := s.errorClasses ++ [info] } ∧ info.name = name ∧
      (∀ c ∈ s.errorClasses, c.name ≠ name) ∧ isGlobalName name = false ∧
      (Eval.ctorParams ctor).map (fun p => (p.param.name, p.readonly)) = info.params.map fun x => (x.1, x.2.2) := by
  unfold translateErrorClass at h
  simp only [bind_ok, ite_state] at h
  obtain ⟨name', s₁, hname, h⟩ := h
  obtain ⟨rfl, rfl⟩ := checkName_ok hname
  split at h
  · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at h
  simp only [pure_bind, bind_ok, get_ok, modify_ok, pure_ok] at h
  obtain ⟨u, s₂, htop, params, s₃, hparams, c, s₄, ⟨rfl, rfl⟩, u', s₅, rfl, rfl, rfl⟩ := h
  obtain ⟨rfl, -⟩ := declareTopLevel_ok htop
  obtain ⟨rfl, s₆, hparams⟩ := isolated_ok hparams
  refine ⟨rfl, rfl, declareTopLevel_classes htop, declareTopLevel_global htop, ?_⟩
  cases ctor with
  | none =>
    simp only [pure_ok] at hparams
    obtain ⟨rfl, -⟩ := hparams
    rfl
  | some pm =>
    obtain ⟨ps, message⟩ := pm
    simp only [bind_ok, ite_state] at hparams
    obtain ⟨params', s₇, hps, hparams⟩ := hparams
    split at hparams
    · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at hparams
    · split at hparams
      · simp only [bind_ok, get_ok, fuelLimit_ok] at hparams
        obtain ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, code, s₈, -, hparams⟩ := hparams
        simp only [ite_state] at hparams
        split at hparams
        · simp only [pure_ok] at hparams
          obtain ⟨rfl, -⟩ := hparams
          exact (ctorParams_shape ps _ _ _ hps).symm
        · simp at hparams
      · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at hparams

/-- What the error classes among `ds` do to the state: they add themselves to
the error classes, in order, and change nothing else. Each has a name that no
class before it has and that is not a global's, and its parameters are those
of its constructor, the first of its name among `ds`. -/
theorem errorClasses_ok : ∀ (ds : List Decl) (s s' : Ctx) (os : List (Option ClassInfo)),
    ds.mapM translateErrorClass? s = .ok os s' →
    s' = { s with errorClasses := s.errorClasses ++ os.filterMap id } ∧
      ∀ c ∈ os.filterMap id, c.name ∉ s.errorClasses.map (·.name) ∧ isGlobalName c.name = false ∧
        ∃ ctor, Eval.errorClassOfDecls c.name ds = some ctor ∧
          (Eval.ctorParams ctor).map (fun p => (p.param.name, p.readonly)) = c.params.map fun x => (x.1, x.2.2)
  | [], s, s', os, h => by
    simp only [List.mapM_nil, pure_ok] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, by simp⟩
  | d :: ds, s, s', os, h => by
    simp only [List.mapM_cons, bind_ok, pure_ok] at h
    obtain ⟨o, s₁, ho, os', s₂, hos, rfl, rfl⟩ := h
    obtain ⟨rfl, hrest⟩ := errorClasses_ok ds s₁ s₂ os' hos
    cases d
    case errorClass sp ex n ctor =>
      simp only [translateErrorClass?, map_ok] at ho
      obtain ⟨info, hinfo, rfl⟩ := ho
      obtain ⟨rfl, hn, hnew, hglob, hshape⟩ := translateErrorClass_ok hinfo
      refine ⟨by simp, fun c hc => ?_⟩
      simp only [List.filterMap_cons, id_eq, List.mem_cons] at hc
      rcases hc with rfl | hc
      · refine ⟨fun hm => ?_, hn ▸ hglob, ctor, ?_, hshape⟩
        · obtain ⟨c', hc', he⟩ := List.mem_map.mp hm
          exact hnew c' hc' (he.trans hn)
        · simp [Eval.errorClassOfDecls, hn]
      · obtain ⟨hm, hg, ctor', hfind, hshape'⟩ := hrest c hc
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton,
          not_or] at hm
        refine ⟨hm.1, hg, ctor', ?_, hshape'⟩
        have hne : n ≠ c.name := by rw [← hn]; exact fun h => hm.2 h.symm
        simp [Eval.errorClassOfDecls, hne, hfind]
    all_goals
      simp only [translateErrorClass?, pure_ok] at ho
      obtain ⟨rfl, rfl⟩ := ho
      refine ⟨by simp, fun c hc => ?_⟩
      simp only [List.filterMap_cons, id_eq] at hc
      obtain ⟨hm, hg, ctor', hfind, hshape'⟩ := hrest c hc
      exact ⟨hm, hg, ctor', by simpa [Eval.errorClassOfDecls] using hfind, hshape'⟩

/-- `translateErrorTypes` records the error classes of `m` and changes
nothing else; its output has no function. When no class was recorded before,
each class recorded is one that `m` declares, with the constructor's
parameters, and no two have one name. -/
theorem translateErrorTypes_ok {m : Module} {s s' : Ctx} {pre : List IR.Decl}
    (h : translateErrorTypes m s = .ok pre s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧ s'.functions = s.functions ∧ s'.enums = s.enums ∧
      s'.enumValues = s.enumValues ∧ IR.functions pre = [] ∧
      (s.errorClasses = [] → ∀ c ∈ s'.errorClasses, isGlobalName c.name = false ∧
        ∃ ctor, Eval.errorClassOf m c.name = some ctor ∧
          (Eval.ctorParams ctor).map (fun p => (p.param.name, p.readonly)) = c.params.map fun x => (x.1, x.2.2)) := by
  unfold translateErrorTypes at h
  simp only [bind_ok] at h
  obtain ⟨os, s₁, hos, h⟩ := h
  obtain ⟨rfl, hcls⟩ := errorClasses_ok m.decls s s₁ os hos
  have hc : ∀ c ∈ ({ s with errorClasses := s.errorClasses ++ os.filterMap id } : Ctx).errorClasses,
      s.errorClasses = [] → isGlobalName c.name = false ∧
        ∃ ctor, Eval.errorClassOf m c.name = some ctor ∧
          (Eval.ctorParams ctor).map (fun p => (p.param.name, p.readonly)) = c.params.map fun x => (x.1, x.2.2) := by
    intro c hc h0
    simp only [h0, List.nil_append] at hc
    exact (hcls c hc).2
  simp only [ite_state] at h
  split at h
  · simp only [pure_ok] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun h0 c hc' => hc c hc' h0⟩
  · simp only [bind_ok, pure_ok] at h
    obtain ⟨_, _, ⟨-, rfl⟩, u, s₂, htop, rfl, rfl⟩ := h
    obtain ⟨rfl, -⟩ := declareTopLevel_ok htop
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun h0 c hc' => hc c hc' h0⟩

/-- A function of `c.withExports L` is one of `c`, exported there or named by
`L` without `type`. -/
theorem mem_withExports_functions {c : Ctx} {L : List ImportName} {g : FnInfo}
    (h : g ∈ (c.withExports L).functions) :
    ∃ f ∈ c.functions, g.name = f.name ∧ g.file = f.file ∧
      (g.exported = true → f.exported = true ∨ f.name ∈ (L.filter (!·.typeOnly)).map (·.name)) := by
  simp only [Ctx.withExports, List.mem_map] at h
  obtain ⟨f, hf, rfl⟩ := h
  refine ⟨f, hf, ?_⟩
  split
  · rename_i hm
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hm
    exact ⟨rfl, rfl, fun _ => .inr hm.2⟩
  · exact ⟨rfl, rfl, .inl⟩

/-- A string enum of `c.withExports L` is one of `c`: an export list does not
export a string enum. -/
theorem mem_withExports_enums {c : Ctx} {L : List ImportName} {e : EnumInfo}
    (h : e ∈ (c.withExports L).enums) (hn : e.named.isSome = true) : e ∈ c.enums := by
  simp only [Ctx.withExports, List.mem_map] at h
  obtain ⟨f, hf, rfl⟩ := h
  by_cases hm : f.named.isNone = true
  · have hnone : f.named = none := Option.isNone_iff_eq_none.mp hm
    split at hn <;> simp [hnone] at hn
  · simp [hm, hf]

/-- A name that an export list of `m` names without `type`. -/
theorem listsExport_of {m : Module} {name : String}
    (h : name ∈ ((exportListed m).filter (!·.typeOnly)).map (·.name)) : Eval.listsExport m name = true := by
  simp only [List.mem_map, List.mem_filter, exportListed, List.mem_flatMap] at h
  obtain ⟨n, ⟨⟨d, hd, hn⟩, ht⟩, rfl⟩ := h
  simp only [Eval.listsExport, List.any_eq_true]
  refine ⟨d, hd, ?_⟩
  rcases d with _ | ⟨_, names, _ | _⟩ | _ | _ | _ | _ | _ <;> simp_all
  exact ⟨n, hn, by simpa using ht⟩

/-- What one declaration does to the state: it keeps the file and the
interfaces, adds its functions at the end, and keeps their names distinct. A
function that it adds as exported is one that it declares as exported. -/
theorem translateDecl_ok {thr : String → Bool} {cls : String → Option (Option (List CtorParam × Expr))}
    {classes : List ClassInfo} {d : Decl} {s s' : Ctx} {o : Option IR.Decl}
    (hself : IfacesSelf s.interfaces) (h : translateDecl thr cls classes d s = .ok o s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧
      ∃ more, s'.functions = s.functions ++ more ∧ (∀ f ∈ more, f.ref ∈ declRefs s.file d) ∧
        ((s.functions.map (·.name)).Nodup → (s'.functions.map (·.name)).Nodup) ∧
        (∀ f ∈ more, f.exported = true → ∃ sp tps ps r b, d = .function sp true f.name tps ps r b) ∧
        (∀ f ∈ more, (f.file = s.file ∧ ∃ sp ex tps ps r b, d = .function sp ex f.name tps ps r b) ∨
          ∃ i, s.interfaces.lookup f.file = some i ∧ ∃ g ∈ i.functions, g.name = f.name) := by
  cases d with
  | «import» sp names source =>
    simp only [translateDecl, bind_ok, pure_ok] at h
    obtain ⟨u, s₁, h₁, rfl, rfl⟩ := h
    obtain ⟨hf, hi, more, hfns, hrefs, hex, hnd, horig⟩ := translateImport_ok hself h₁
    exact ⟨hf, hi, more, hfns, hrefs, hnd, fun f hf' he => by simp [hex f hf'] at he,
      fun f hf' => .inr (horig f hf')⟩
  | interface sp ex name tps fields =>
    simp only [translateDecl, map_ok] at h
    obtain ⟨o', h₁, rfl⟩ := h
    obtain ⟨hf, hi, hfns, -⟩ := translateInterface_ok h₁
    exact ⟨hf, hi, [], by simp [hfns], by simp, by simp [hfns], by simp, by simp⟩
  | typeAlias sp ex name tps type =>
    simp only [translateDecl, map_ok] at h
    obtain ⟨o', h₁, rfl⟩ := h
    obtain ⟨hf, hi, hfns, -⟩ := translateAlias_ok h₁
    exact ⟨hf, hi, [], by simp [hfns], by simp, by simp [hfns], by simp, by simp⟩
  | enum sp ex name members =>
    simp only [translateDecl, map_ok] at h
    obtain ⟨o', h₁, rfl⟩ := h
    obtain ⟨-, -, i, v, -, -, -, -, -, rfl⟩ := translateStringEnum_shape h₁
    exact ⟨rfl, rfl, [], by simp, by simp, by simp, by simp, by simp⟩
  | function sp ex name tps params ret body =>
    simp only [translateDecl, map_ok] at h
    obtain ⟨o', h₁, rfl⟩ := h
    obtain ⟨-, -, hf, hi, hfresh, f, hfns, hfile, hname, hex, -⟩ := translateFunction_ok h₁
    refine ⟨hf, hi, [f], hfns, by simp [declRefs, FnInfo.ref, hfile, hname], fun hnd => ?_, ?_, ?_⟩
    · rw [hfns, List.map_append, List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
      simpa [hname] using hfresh g hg
    · intro g hg he
      simp only [List.mem_singleton] at hg
      subst hg
      rw [hex] at he
      subst he
      exact ⟨sp, tps, params, ret, body, by rw [hname]⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact .inl ⟨hfile, sp, ex, tps, params, ret, body, by rw [hname]⟩
  | exports sp names source =>
    obtain ⟨rfl, rfl⟩ := translateExports_ok h
    exact ⟨rfl, rfl, [], by simp, by simp [declRefs], id, by simp, by simp⟩
  | exportedVar sp decl => simp [translateDecl] at h
  | errorClass _ _ _ _ =>
    simp only [translateDecl, bind_ok, modify_ok, pure_ok] at h
    obtain ⟨_, _, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, [], by simp, by simp, id, by simp, by simp⟩
  | stmt st => simp [translateDecl] at h

/-- What one declaration does to the names and the string enums of the file. -/
theorem translateDecl_names {P : Eval.Program} {thr : String → Bool}
    {cls : String → Option (Option (List CtorParam × Expr))} {classes : List ClassInfo} {d : Decl} {s s' : Ctx}
    {o : Option IR.Decl} (hfe : FaithfulE P s.interfaces) (h : translateDecl thr cls classes d s = .ok o s') :
    DeclNames P d s s' := by
  cases d with
  | «import» sp names source =>
    simp only [translateDecl, bind_ok, pure_ok] at h
    obtain ⟨u, s₁, h₁, rfl, rfl⟩ := h
    exact translateImport_names hfe h₁
  | interface sp ex name tps fields =>
    simp only [translateDecl, map_ok] at h
    obtain ⟨o', h₁, rfl⟩ := h
    exact translateInterface_names h₁
  | typeAlias sp ex name tps type =>
    simp only [translateDecl, map_ok] at h
    obtain ⟨o', h₁, rfl⟩ := h
    exact translateAlias_names h₁
  | enum sp ex name members =>
    simp only [translateDecl, map_ok] at h
    obtain ⟨o', h₁, rfl⟩ := h
    exact translateStringEnum_names h₁
  | exports sp names source =>
    obtain ⟨-, rfl⟩ := translateExports_ok h
    exact ⟨rfl, fun _ h => h, by simp [boundNames], by simp [boundNames], by simp [boundNames],
      ⟨[], by simp, by simp⟩, ⟨[], by simp, by simp⟩⟩
  | function sp ex name tps params ret body =>
    simp only [translateDecl, map_ok] at h
    obtain ⟨o', h₁, rfl⟩ := h
    exact translateFunction_names h₁
  | exportedVar sp decl => simp [translateDecl] at h
  | errorClass _ _ _ _ =>
    simp only [translateDecl, bind_ok, modify_ok, pure_ok] at h
    obtain ⟨_, _, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun _ h => h, by simp [boundNames], by simp [boundNames], by simp [boundNames],
      ⟨[], by simp, by simp⟩, ⟨[], by simp, by simp⟩⟩
  | stmt st => simp [translateDecl] at h

/-- `R` holds for each pair of elements in the same place. -/
def Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Forall₂ R as bs
  | _, _ => False

/-- The output function `out` is the translation of the source function
`src`: the same name, the same parameters, and a body that the translator made
from the source body, in a scope of exactly the parameters, of functions of
`F` and of enum values of `E`. -/
def FnRelIn (F : List FnInfo) (E : List EnumValue) (C : List ClassInfo) (src : String × List String × Stmt)
    (out : String × List String × IR.Body) : Prop :=
  src.1 = out.1 ∧ src.2.1 = out.2.1 ∧
    (∃ Fu env c c', translateStatements Fu env .ret (blockStatements src.2.2) c = .ok out.2.2 c' ∧
      (∀ g ∈ env.functions, g ∈ F) ∧ (∀ e ∈ env.enums, e ∈ E) ∧ (∀ k ∈ env.classes, k ∈ C) ∧
      ∀ x, env.has x = decide (x ∈ src.2.1)) ∧
    Stmt.ownsChanges src.2.1 src.2.2 = true

theorem functions_append (a b : List IR.Decl) : IR.functions (a ++ b) = IR.functions a ++ IR.functions b :=
  List.filterMap_append

theorem Forall₂.mono {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, Forall₂ R l₁ l₂ → Forall₂ S l₁ l₂
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hab, hr⟩ => ⟨h _ _ hab, Forall₂.mono h hr⟩
  | [], _ :: _, h' | _ :: _, [], h' => h'.elim

/-- What a list of declarations does to the state, and how its functions
translate. -/
theorem decls_ok (P : Eval.Program) (thr : String → Bool) (cls : String → Option (Option (List CtorParam × Expr)))
    (classes : List ClassInfo) :
    ∀ (ds : List Decl) (s s' : Ctx) (os : List (Option IR.Decl)),
    IfacesSelf s.interfaces → FaithfulE P s.interfaces → ds.mapM (translateDecl thr cls classes) s = .ok os s' →
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧
      (∃ more, s'.functions = s.functions ++ more ∧ (∀ f ∈ more, f.ref ∈ ds.flatMap (declRefs s.file)) ∧
        (∀ f ∈ more, f.exported = true → ∃ sp tps ps r b, Decl.function sp true f.name tps ps r b ∈ ds) ∧
        ∀ f ∈ more, (f.file = s.file ∧ ∃ sp ex tps ps r b, Decl.function sp ex f.name tps ps r b ∈ ds) ∨
          ∃ i, s.interfaces.lookup f.file = some i ∧ ∃ g ∈ i.functions, g.name = f.name) ∧
      ((s.functions.map (·.name)).Nodup → (s'.functions.map (·.name)).Nodup) ∧
      DeclsNames P ds s s' ∧
      Forall₂ (FnRelIn s'.functions s'.enumValues classes) (Eval.functionsIn thr cls ds)
        (IR.functions (os.filterMap id))
  | [], s, s', os, _, _, h => by
    simp only [List.mapM_nil, pure_ok] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, ⟨[], by simp, by simp, by simp, by simp⟩, id, DeclsNames.nil P s,
      by simp [Eval.functionsIn, IR.functions]; trivial⟩
  | d :: ds, s, s', os, hself, hfe, h => by
    simp only [List.mapM_cons, bind_ok, pure_ok] at h
    obtain ⟨o, s₁, h₁, os', s₂, h₂, rfl, rfl⟩ := h
    obtain ⟨hf₁, hi₁, more₁, hfns₁, hrefs₁, hnd₁, hex₁, hor₁⟩ := translateDecl_ok hself h₁
    have hn₁ := translateDecl_names hfe h₁
    obtain ⟨hf₂, hi₂, ⟨more₂, hfns₂, hrefs₂, hex₂, hor₂⟩, hnd₂, hn₂, hrel⟩ :=
      decls_ok P thr cls classes ds s₁ s₂ os' (by rw [hi₁]; exact hself) (by rw [hi₁]; exact hfe) h₂
    refine ⟨hf₂.trans hf₁, hi₂.trans hi₁, ⟨more₁ ++ more₂, by rw [hfns₂, hfns₁, List.append_assoc],
      ?_, ?_, ?_⟩, fun h => hnd₂ (hnd₁ h), DeclsNames.cons hn₁ hn₂, ?_⟩
    · intro f hf
      rw [List.flatMap_cons, List.mem_append]
      rcases List.mem_append.mp hf with hf | hf
      · exact .inl (hrefs₁ f hf)
      · exact .inr (by rw [← hf₁]; exact hrefs₂ f hf)
    · intro f hf he
      rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨sp, tps, ps, r, b, hd⟩ := hex₁ f hf he
        exact ⟨sp, tps, ps, r, b, by rw [hd]; exact List.mem_cons_self ..⟩
      · obtain ⟨sp, tps, ps, r, b, hd⟩ := hex₂ f hf he
        exact ⟨sp, tps, ps, r, b, List.mem_cons_of_mem _ hd⟩
    · intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · rcases hor₁ f hf with ⟨hfl, sp, ex, tps, ps, r, b, hd⟩ | h
        · exact .inl ⟨hfl, sp, ex, tps, ps, r, b, by rw [hd]; exact List.mem_cons_self ..⟩
        · exact .inr h
      · rcases hor₂ f hf with ⟨hfl, sp, ex, tps, ps, r, b, hd⟩ | h
        · exact .inl ⟨hfl.trans hf₁, sp, ex, tps, ps, r, b, List.mem_cons_of_mem _ hd⟩
        · exact .inr (by rw [← hi₁]; exact h)
    · -- The functions of the head, then the rest.
      have hsub : ∀ g ∈ s₁.functions, g ∈ s₂.functions := fun g hg => by
        rw [hfns₂]; exact List.mem_append_left _ hg
      have hsubE : ∀ e ∈ s.enumValues, e ∈ s₂.enumValues := fun e he => by
        obtain ⟨m₁, e₁, -⟩ := hn₁.values
        obtain ⟨m₂, e₂, -⟩ := hn₂.values
        rw [e₂, e₁]; exact List.mem_append_left _ (List.mem_append_left _ he)
      cases d with
      | function sp ex name tps params ret body =>
        simp only [translateDecl, map_ok] at h₁
        obtain ⟨o', h₁, rfl⟩ := h₁
        obtain ⟨-, -, -, -, -, f, hfns, -, -, -, lp, r, out, rfl, hlp, Fu, env, c, c', ht, henv, henvE, henvC,
          hhas, hown⟩ := translateFunction_ok h₁
        simp only [Eval.functionsIn, IR.functions, List.filterMap_cons] at hrel ⊢
        refine ⟨⟨rfl, hlp.symm, ⟨Fu, env, c, c', ht, fun g hg => ?_, fun e he => ?_,
          fun k hk => by rwa [henvC] at hk, hhas⟩, hown⟩, hrel⟩
        · rw [henv] at hg
          exact hsub g (by rw [hfns]; exact hg)
        · rw [henvE] at he
          exact hsubE e he
      | «import» sp names source =>
        simp only [translateDecl, bind_ok, pure_ok] at h₁
        obtain ⟨u, s₃, -, rfl, -⟩ := h₁
        simpa [Eval.functionsIn, IR.functions, List.filterMap_cons] using hrel
      | interface sp ex name tps fields =>
        simp only [translateDecl, map_ok] at h₁
        obtain ⟨o', h₁, rfl⟩ := h₁
        obtain ⟨-, -, -, n, tps', fs, rfl⟩ := translateInterface_ok h₁
        simpa [Eval.functionsIn, IR.functions, List.filterMap_cons] using hrel
      | typeAlias sp ex name tps type =>
        simp only [translateDecl, map_ok] at h₁
        obtain ⟨o', h₁, rfl⟩ := h₁
        obtain ⟨-, -, -, ⟨n, tps', t, rfl⟩ | ⟨n, ms, rfl⟩ | ⟨n, f, ps, rfl⟩ | ⟨n, tps', fs, rfl⟩⟩ :=
            translateAlias_ok h₁ <;>
          simpa [Eval.functionsIn, IR.functions, List.filterMap_cons] using hrel
      | exports sp names source =>
        obtain ⟨rfl, rfl⟩ := translateExports_ok h₁
        simpa [Eval.functionsIn, IR.functions, List.filterMap_cons] using hrel
      | enum sp ex name members =>
        simp only [translateDecl, map_ok] at h₁
        obtain ⟨o', h₁, rfl⟩ := h₁
        obtain ⟨-, rfl, -⟩ := translateStringEnum_shape h₁
        simpa [Eval.functionsIn, IR.functions, List.filterMap_cons] using hrel
      | exportedVar sp decl => simp [translateDecl] at h₁
      | errorClass _ _ _ _ =>
        simp only [translateDecl, bind_ok, modify_ok, pure_ok] at h₁
        obtain ⟨_, _, rfl, rfl, rfl⟩ := h₁
        simpa [Eval.functionsIn, IR.functions, List.filterMap_cons] using hrel
      | stmt st => simp [translateDecl] at h₁

theorem findSome_eq {α β : Type} {f : α → Option β} {x : β} :
    ∀ {l : List α}, (∃ a ∈ l, (f a).isSome) → (∀ a ∈ l, ∀ y, f a = some y → y = x) →
      l.findSome? f = some x
  | [], ⟨a, ha, _⟩, _ => by simp at ha
  | a :: l, hex, huniq => by
    simp only [List.findSome?_cons]
    cases hfa : f a with
    | some y => simp [huniq a (List.mem_cons_self ..) y hfa]
    | none =>
      simp only
      refine findSome_eq ?_ fun b hb y hy => huniq b (List.mem_cons_of_mem _ hb) y hy
      obtain ⟨b, hb, hsome⟩ := hex
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [hfa] at hsome; simp at hsome
      · exact ⟨b, hb, hsome⟩

/-- The interfaces offer only functions that the program's files export. -/
def Faithful (p : Eval.Program) (ifaces : List (String × Interface)) : Prop :=
  ∀ t i, ifaces.lookup t = some i → ∀ g ∈ i.functions,
    ∃ tm, p.lookup t = some tm ∧ Eval.exportsFunction tm g.name = true

/-- A function that a declaration adds is named by a name that it binds. -/
theorem declRefs_bound {file : String} {d : Decl} {r : DeclRef} (h : r ∈ declRefs file d) :
    r.name ∈ boundNames d := by
  cases d with
  | function sp ex name tps ps rt b =>
    simp only [declRefs, List.mem_singleton] at h
    subst h
    simp [boundNames]
  | «import» sp names source =>
    simp only [declRefs] at h
    split at h
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h
      simp only [boundNames, List.mem_map]
      exact ⟨n, (List.mem_filter.mp hn).1, rfl⟩
    · simp at h
  | _ => simp [declRefs] at h

/-- Every function that a file's translation knows is the one that a call of its
name runs in that file. The module binds each name once, so the declaration
that a function comes from is the only one that binds its name. -/
theorem module_resolves {p : Eval.Program} {file : String} {m : Module} (hp : p.lookup file = some m)
    {ifaces : List (String × Interface)} (hfaith : Faithful p ifaces) {F : List FnInfo}
    (hincl : ∀ f ∈ F, f.ref ∈ m.decls.flatMap (declRefs file)) (hbn : (m.decls.flatMap boundNames).Nodup)
    (horig : ∀ f ∈ F, (f.file = file ∧ ∃ sp ex tps ps r b, Decl.function sp ex f.name tps ps r b ∈ m.decls) ∨
      ∃ i, ifaces.lookup f.file = some i ∧ ∃ g ∈ i.functions, g.name = f.name) :
    ∀ f ∈ F, Eval.resolve ⟨p, file⟩ f.name = some f.ref := by
  intro f hf
  obtain ⟨df, hdf, hrdf⟩ := List.mem_flatMap.mp (hincl f hf)
  have hbf : f.name ∈ boundNames df := declRefs_bound hrdf
  have hown_iff : ((Eval.functions m).any fun x => x.fst == f.name) = true ↔
      ∃ sp ex tps ps r b, Decl.function sp ex f.name tps ps r b ∈ m.decls := by
    simp only [List.any_eq_true, beq_iff_eq, Eval.functions, Eval.functionsIn, List.mem_filterMap]
    constructor
    · rintro ⟨⟨n, ps, b⟩, ⟨d, hd, hsel⟩, rfl⟩
      cases d <;> simp at hsel
      obtain ⟨rfl, -, rfl⟩ := hsel
      exact ⟨_, _, _, _, _, _, hd⟩
    · rintro ⟨sp, ex, tps, ps, r, b, hd⟩
      exact ⟨(f.name, ps.map (·.name), Eval.Stmt.hoisted (Eval.mayThrow m) (Eval.errorClassOf m) b), ⟨_, hd, rfl⟩, rfl⟩
  unfold Eval.resolve
  simp only [hp, Option.bind_eq_bind, Option.bind_some]
  by_cases hown : ((Eval.functions m).any fun x => x.fst == f.name) = true
  · rw [if_pos hown]
    obtain ⟨sp, ex, tps, ps, r, b, hd⟩ := hown_iff.mp hown
    have := bound_unique hbn hdf hd hbf (by simp [boundNames])
    subst this
    simp only [declRefs, List.mem_singleton] at hrdf
    rw [hrdf]
    rfl
  · rw [if_neg hown]
    have hnot : ¬ ∃ sp ex tps ps r b, Decl.function sp ex f.name tps ps r b ∈ m.decls :=
      fun h => hown (hown_iff.mpr h)
    obtain ⟨i, hi, g, hg, hgn⟩ := (horig f hf).resolve_left fun h => hnot h.2
    obtain ⟨tm, htm, hexp⟩ := hfaith _ _ hi g hg
    rw [hgn] at hexp
    rw [findSome_eq (l := m.decls) (x := f.file) ?ex ?uniq]
    · simp only [Option.bind_some, htm, hexp, if_true]
      rfl
    case ex =>
      refine ⟨df, hdf, ?_⟩
      cases df with
      | function sp ex name tps ps r b =>
        simp only [declRefs, List.mem_singleton, FnInfo.ref, DeclRef.mk.injEq] at hrdf
        exact absurd ⟨sp, ex, tps, ps, r, b, hrdf.2 ▸ hdf⟩ hnot
      | «import» sp names source =>
        simp only [declRefs] at hrdf
        split at hrdf
        · rename_i target htarget
          obtain ⟨n, hn, hnr⟩ := List.mem_map.mp hrdf
          simp only [List.mem_filter] at hn
          simp only [FnInfo.ref, DeclRef.mk.injEq] at hnr
          have hany : (names.any fun n => !n.typeOnly && n.name == f.name) = true :=
            List.any_eq_true.mpr ⟨n, hn.1, by simpa [hnr.2] using hn.2⟩
          simp [hany, htarget]
        · simp at hrdf
      | _ => simp [declRefs] at hrdf
    case uniq =>
      intro d hd y hy
      cases d with
      | «import» sp names source =>
        simp only at hy
        split at hy
        · rename_i hany
          obtain ⟨n, hn, hnn⟩ := List.any_eq_true.mp hany
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hnn
          have hbd : f.name ∈ boundNames (.import sp names source) := by
            simp only [boundNames, List.mem_map]
            exact ⟨n, hn, hnn.2⟩
          have := bound_unique hbn hd hdf hbd hbf
          subst this
          simp only [declRefs, hy] at hrdf
          obtain ⟨n', -, hnr⟩ := List.mem_map.mp hrdf
          simp only [FnInfo.ref, DeclRef.mk.injEq] at hnr
          exact hnr.1
        · simp at hy
      | _ => simp at hy

/-- Every string enum whose members a file's code may read is the one that its
name reads in that file: the only declaration that binds the name binds it to
the enum. -/
theorem module_resolvesE {p : Eval.Program} {file : String} {m : Module} (hp : p.lookup file = some m)
    (hbn : (m.decls.flatMap boundNames).Nodup) {E : List EnumValue}
    (hE : ∀ e ∈ E, ∃ d ∈ m.decls, Eval.enumBinding p file e.name d = some (some e.members)) :
    ∀ e ∈ E, Eval.resolveEnum ⟨p, file⟩ e.name = some e.members := by
  intro e he
  obtain ⟨d, hd, hb⟩ := hE e he
  unfold Eval.resolveEnum
  simp only [hp, Option.bind_eq_bind, Option.bind_some]
  rw [findSome_eq (x := some e.members) ⟨d, hd, by rw [hb]; rfl⟩ ?_]
  · rfl
  · intro d' hd' y hy
    have := bound_unique hbn hd' hd (enumBinding_bound (by rw [hy]; rfl)) (enumBinding_bound (by rw [hb]; rfl))
    subst this
    rw [hb] at hy
    cases hy
    rfl

/-- The exported enum of a module, by its name, when the module binds each name
once. -/
theorem enumsOf_lookup {sp : Span} {name : String} {ms : List EnumMember} :
    ∀ {ds : List Decl}, (ds.flatMap boundNames).Nodup → Decl.enum sp true name ms ∈ ds →
      (Eval.enumsOf ⟨ds⟩ true).lookup name = some (ms.map fun x => (x.name, x.value))
  | [], _, h => by simp at h
  | d :: ds, hn, h => by
    simp only [List.flatMap_cons, List.nodup_append] at hn
    obtain ⟨-, hn₂, hdis⟩ := hn
    rcases List.mem_cons.mp h with rfl | h
    · simp [Eval.enumsOf]
    · have ih := enumsOf_lookup hn₂ h
      have hname : name ∉ boundNames d := fun hd =>
        hdis _ hd _ (List.mem_flatMap.mpr ⟨_, h, by simp [boundNames]⟩) rfl
      simp only [Eval.enumsOf] at ih ⊢
      cases d with
      | enum sp' ex' name' ms' =>
        have hne : (name == name') = false := by
          have : name ≠ name' := fun e => hname (by simp [boundNames, e])
          simpa using this
        cases ex'
        · simpa [List.filterMap_cons] using ih
        · simp only [List.filterMap_cons, Bool.true_or, ↓reduceIte, List.lookup, hne]
          exact ih
      | _ => simpa [List.filterMap_cons] using ih

/-! ### Programs -/

/-- The output function `out` is the translation of the source function `src`
of a program: the same key, the same parameters, and a body that the
translator made from the source body. Its scope binds exactly the parameters,
and each function it may call is the one that a call of that name runs in its
file. -/
def FnRelP (p : Eval.Program) (src : DeclRef × List String × Stmt)
    (out : DeclRef × List String × IR.Body) : Prop :=
  src.1 = out.1 ∧ src.2.1 = out.2.1 ∧
    (∃ Fu env c c', translateStatements Fu env .ret (blockStatements src.2.2) c = .ok out.2.2 c' ∧
      Resolves ⟨p, src.1.file⟩ env ∧ ∀ x, env.has x = decide (x ∈ src.2.1)) ∧
    Stmt.ownsChanges src.2.1 src.2.2 = true

theorem Forall₂.append {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β} {c : List α} {d : List β},
      Forall₂ R a b → Forall₂ R c d → Forall₂ R (a ++ c) (b ++ d)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, ⟨hab, h⟩, hcd => ⟨hab, Forall₂.append h hcd⟩
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => h.elim

theorem Forall₂.map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (h : ∀ x y, R x y → S (f x) (g y)) :
    ∀ {a : List α} {b : List β}, Forall₂ R a b → Forall₂ S (a.map f) (b.map g)
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hab, hr⟩ => ⟨h _ _ hab, Forall₂.map h hr⟩
  | [], _ :: _, h' | _ :: _, [], h' => h'.elim

theorem lookup_rel {p : Eval.Program} :
    ∀ {srcs : List (DeclRef × List String × Stmt)} {outs : List (DeclRef × List String × IR.Body)},
      Forall₂ (FnRelP p) srcs outs → ∀ {key : DeclRef} {ps : List String} {b : IR.Body},
        outs.lookup key = some (ps, b) →
        ∃ bS, srcs.lookup key = some (ps, bS) ∧ FnRelP p (key, ps, bS) (key, ps, b)
  | [], [], _, _, _, _, h => by simp at h
  | (n, ps', bS) :: srcs, (n', ps'', b') :: outs, ⟨⟨hn, hps, hrel⟩, hrest⟩, key, ps, b, h => by
    simp only at hn hps
    subst hn hps
    by_cases hk : key = n
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨bS, ⟨rfl, rfl⟩, rfl, rfl, hrel⟩
    · have : (key == n) = false := beq_eq_false_iff_ne.mpr hk
      simp only [List.lookup, this] at h ⊢
      exact lookup_rel hrest h
  | [], _ :: _, h, _, _, _, _ | _ :: _, [], h, _, _, _, _ => h.elim

theorem lookup_isSome {β : Type} (x : String) (l : List (String × β)) :
    (l.lookup x).isSome = decide (x ∈ l.map Prod.fst) := by
  rw [Bool.eq_iff_iff, List.lookup_isSome_iff]
  simp only [decide_eq_true_eq, List.mem_map, beq_iff_eq]
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩⟩

section Calls

variable {N : Type} [JSNumber N]

omit [JSNumber N] in
theorem scoped_params {m : Eval.Scope} {env : Translate.Env} {ps : List String} {vs : List (Val N)}
    (henv : ∀ x, env.has x = decide (x ∈ ps)) (hres : Resolves m env) (hlen : ps.length = vs.length) :
    Scoped m env ((ps.zip vs).reverse) :=
  ⟨fun x => by
    rw [lookup_isSome, henv, List.map_reverse, List.map_fst_zip (by omega)]
    simp, hres⟩

variable (p : Eval.Program) (fs : List (DeclRef × List String × IR.Body))

/-- Every call of the output gives what the same call of the source gives,
for every fuel. -/
theorem calls_agree (hrel : Forall₂ (FnRelP p) (Eval.functionsOf p) fs) :
    ∀ fuel, CallsAgree (N := N) p fs fuel
  | 0 => fun key vs v h => by simp [callO] at h
  | fuel + 1 => fun key vs v h => by
    have hc : ∀ k ≤ fuel, CallsAgree (N := N) p fs k := fun k hk => calls_agree hrel k
    simp only [callO] at h
    cases hl : fs.lookup key with
    | none => simp [hl] at h
    | some pb =>
      obtain ⟨ps, b⟩ := pb
      simp only [hl, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · simp at h
      · rename_i hlen
        cases hb : IR.Body.exec fs fuel (ps.zip vs).reverse b with
        | none => simp [hb] at h
        | some o =>
          cases o with
          | normal _ | brk _ | cont _ => simp [hb] at h
          | ret w =>
            simp [hb] at h
            subst h
            obtain ⟨bS, hlS, -, -, ⟨F, env, ctx, ctx', htr, hres, henv⟩, hown⟩ := lookup_rel hrel hl
            have hlen' : ps.length = vs.length := by simpa using hlen
            have hsim := (stmts_sound ⟨p, key.file⟩ fs F fuel hc).1 _ _ _ _ _ _ htr
            have hex := (hsim _ _ (fun _ => rfl) (scoped_params henv hres hlen')).1 w hb
            have hst := block_ret ⟨p, key.file⟩ fuel bS hex
            simp [callS, hlS, hlen', hst, hown]

end Calls

/-- The translation of a program, file by file. Each file's translation starts
with no functions, no literal unions, no enum values and no error classes,
and with the interfaces of the files before it. -/
inductive ProgramTranslation :
    Eval.Program → List (String × List IR.Decl) → List (String × Interface) → Prop
  | nil : ProgramTranslation [] [] []
  | snoc {p : Eval.Program} {outs : List (String × List IR.Decl)} {ifaces : List (String × Interface)}
      {file : String} {m : Module} {decls : List IR.Decl} {start finish : Ctx}
      (usesNumber : Bool) (numberVar : String) :
      ProgramTranslation p outs ifaces → start.file = file →
      (start.functions, start.enums, start.enumValues, start.errorClasses) = ([], [], [], []) →
      start.interfaces = ifaces → translateDecls m start = .ok decls finish →
      ProgramTranslation (p ++ [(file, m)]) (outs ++ [(file, decls)])
        (ifaces ++ [(file, (finish.withExports (exportListed m)).interface usesNumber numberVar (reexportListed m))])

theorem lookup_append_some {β : Type} {k : String} {b : β} {l l' : List (String × β)}
    (h : l.lookup k = some b) : (l ++ l').lookup k = some b := by
  rw [List.lookup_append, h]; rfl

theorem lookup_none_of_not_mem {β : Type} {k : String} {l : List (String × β)}
    (h : k ∉ l.map Prod.fst) : l.lookup k = none := by
  rw [List.lookup_eq_none_iff]
  intro p hp
  simp only [bne_iff_ne, ne_eq]
  rintro rfl
  exact h (List.mem_map_of_mem hp)

theorem lookup_append_none {β : Type} {k : String} {l l' : List (String × β)}
    (h : k ∉ l.map Prod.fst) : (l ++ l').lookup k = l'.lookup k := by
  rw [List.lookup_append, lookup_none_of_not_mem h]; rfl

theorem lookup_append_mem {β : Type} {k : String} {l l' : List (String × β)}
    (h : k ∈ l.map Prod.fst) : (l ++ l').lookup k = l.lookup k := by
  rw [List.lookup_append]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (by rw [lookup_isSome]; simpa using h)
  rw [hb]; rfl

/-- What a program's translation gives: interfaces that name their files and
that the program's files export, and output functions that are the
translations of the program's functions. -/
theorem programTranslation_rel {p : Eval.Program} {outs : List (String × List IR.Decl)}
    {ifaces : List (String × Interface)} (h : ProgramTranslation p outs ifaces) :
    ∀ (P : Eval.Program), (p.map (·.1)).Nodup → (∀ t tm, p.lookup t = some tm → P.lookup t = some tm) →
      ifaces.map (·.1) = p.map (·.1) ∧ outs.map (·.1) = p.map (·.1) ∧ IfacesSelf ifaces ∧ Faithful P ifaces ∧
        FaithfulE P ifaces ∧ Forall₂ (FnRelP P) (Eval.functionsOf p) (IR.functionsOf outs) := by
  induction h with
  | nil =>
    intro P _ _
    exact ⟨rfl, rfl, fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ _ h => by simp at h, trivial⟩
  | @snoc p outs ifaces file m decls start finish u nv hrest hfile hfns hifaces htr ih =>
    intro P hnd hP
    simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append, List.mem_singleton] at hnd
    have hnotin : file ∉ p.map (·.1) := fun h => hnd.2.2 _ h _ rfl rfl
    have hP' : ∀ t tm, p.lookup t = some tm → P.lookup t = some tm := fun t tm h =>
      hP t tm (lookup_append_some h)
    obtain ⟨hik, hok, hself, hfaith, hfaithE, hrel⟩ := ih P hnd.1 hP'
    have hPm : P.lookup file = some m := hP file m (by rw [lookup_append_none hnotin]; simp)
    simp only [Prod.mk.injEq] at hfns
    obtain ⟨hfns, hen0, hev0, hcls0⟩ := hfns
    -- The file's error classes, then its own translation.
    obtain ⟨pre, s₁, os, hpre, hos, rfl⟩ := translateDecls_ok htr
    obtain ⟨hf₁, hi₁, hfn₁, hen₁, hev₁, hpre0, hcls⟩ := translateErrorTypes_ok hpre
    have hfile : s₁.file = file := hf₁.trans hfile
    have hfns : s₁.functions = [] := hfn₁.trans hfns
    have hen0 : s₁.enums = [] := hen₁.trans hen0
    have hev0 : s₁.enumValues = [] := hev₁.trans hev0
    have hifaces : s₁.interfaces = ifaces := hi₁.trans hifaces
    obtain ⟨hf, hi, ⟨more, hfns', hrefs, hex, horig⟩, -, hnames, hrelm⟩ :=
      decls_ok P (Eval.mayThrow m) (Eval.errorClassOf m) s₁.errorClasses m.decls s₁ finish os
        (by rw [hifaces]; exact hself) (by rw [hifaces]; exact hfaithE) hos
    rw [hfns, List.nil_append] at hfns'
    have hresC : ∀ c ∈ s₁.errorClasses, ClassAgrees ⟨P, file⟩ c := by
      intro c hc
      obtain ⟨hg, ctor, hctor, hshape⟩ := hcls hcls0 c hc
      exact ⟨ctor, by simp [Eval.errorClassIn, hPm, hctor], hshape, hg⟩
    have hbn := hnames.nodup
    have hres : ∀ f ∈ finish.functions, Eval.resolve ⟨P, file⟩ f.name = some f.ref := by
      rw [hfns']
      refine module_resolves hPm (ifaces := ifaces) hfaith (fun f hf' => by rw [← hfile]; exact hrefs f hf') hbn ?_
      intro f hf'
      rcases horig f hf' with ⟨hfl, hd⟩ | ⟨i, hi', hg⟩
      · exact .inl ⟨hfl.trans hfile, hd⟩
      · exact .inr ⟨i, by rw [← hifaces]; exact hi', hg⟩
    have hresE : ∀ e ∈ finish.enumValues, Eval.resolveEnum ⟨P, file⟩ e.name = some e.members := by
      obtain ⟨moreE, hmoreE, hv⟩ := hnames.values
      rw [hmoreE, hev0, List.nil_append]
      refine module_resolvesE hPm hbn fun e he => ?_
      rw [← hfile]
      exact hv e he
    have hkeys : file ∉ ifaces.map (·.1) := by rw [hik]; exact hnotin
    refine ⟨by simp [hik], by simp [hok], ?_, ?_, ?_, ?_⟩
    · intro t i hti g hg
      by_cases ht : t ∈ ifaces.map (·.1)
      · exact hself t i (by rwa [lookup_append_mem ht] at hti) g hg
      · rw [lookup_append_none ht] at hti
        simp only [List.lookup] at hti
        split at hti
        · rename_i hte
          simp only [Option.some.injEq] at hti
          subst hti
          simp only [Ctx.interface, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hg
          have hgf : g.file = finish.file := hg.2.2
          rw [hgf, hf, hfile]
          exact (by simpa using hte : t = file).symm
        · simp at hti
    · intro t i hti g hg
      by_cases ht : t ∈ ifaces.map (·.1)
      · exact hfaith t i (by rwa [lookup_append_mem ht] at hti) g hg
      · rw [lookup_append_none ht] at hti
        simp only [List.lookup] at hti
        split at hti
        · rename_i hte
          have hte : t = file := by simpa using hte
          subst hte
          simp only [Option.some.injEq] at hti
          subst hti
          simp only [Ctx.interface, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hg
          obtain ⟨hgm, hge, hgf⟩ := hg
          obtain ⟨f, hf₀, hn, hgf₀, hex'⟩ := mem_withExports_functions hgm
          rw [hfns'] at hf₀
          refine ⟨m, hPm, ?_⟩
          simp only [Eval.exportsFunction, List.any_eq_true]
          rcases hex' hge with he | hl
          · obtain ⟨sp, tps, ps, r, b, hd⟩ := hex f hf₀ he
            exact ⟨_, hd, by simp [hn]⟩
          · rcases horig f hf₀ with ⟨-, sp, ex, tps, ps, r, b, hd⟩ | ⟨i, hi', -⟩
            · refine ⟨_, hd, ?_⟩
              simp [hn, listsExport_of hl]
            · have hff : f.file = t := by
                have hgf' : g.file = finish.file := hgf
                rw [← hgf₀, hgf', hf, hfile]
              rw [hff, hifaces, lookup_none_of_not_mem hkeys] at hi'
              cases hi'
        · simp at hti
    · intro t i hti name info pairs hse
      by_cases ht : t ∈ ifaces.map (·.1)
      · exact hfaithE t i (by rwa [lookup_append_mem ht] at hti) name info pairs hse
      · rw [lookup_append_none ht] at hti
        simp only [List.lookup] at hti
        split at hti
        · rename_i hte
          have hte : t = file := by simpa using hte
          subst hte
          simp only [Option.some.injEq] at hti
          subst hti
          obtain ⟨hmem, hn, hex', hnamed⟩ := stringEnum_some hse
          simp only [Ctx.interface, Ctx.reachableEnums, List.mem_filter] at hmem
          obtain ⟨moreI, hmoreI, hx⟩ := hnames.exports
          have hmem' := mem_withExports_enums hmem.1 (by simp [hnamed])
          rw [hmoreI, hen0, List.nil_append] at hmem'
          obtain ⟨sp, ms, hd, hms⟩ := hx info hmem' hex' pairs hnamed
          refine ⟨m, hPm, ?_⟩
          rw [← hn, ← hms]
          exact enumsOf_lookup hbn hd
        · simp at hti
    · simp only [Eval.functionsOf, IR.functionsOf, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rw [functions_append, hpre0, List.nil_append]
      refine hrel.append (Forall₂.map ?_ hrelm)
      intro x y hxy
      obtain ⟨hn, hps, ⟨Fu, env, c, c', ht, hsub, hsubE, hsubC, hhas⟩, hown⟩ := hxy
      exact ⟨by simp [hn], hps, ⟨Fu, env, c, c', ht,
        ⟨fun g hg => hres g (hsub g hg), fun e he => hresE e (hsubE e he), fun k hk => hresC k (hsubC k hk)⟩,
        hhas⟩, hown⟩

variable {N : Type} [JSNumber N]

/-- The translator is sound for a program. When it translates every file of a
program, a call of a function of the output returns or throws a value only
when the same call of the program returns or throws the same value in the
interpreter, for all arguments and all fuel. -/
theorem program_sound_call {p : Eval.Program} {outs : List (String × List IR.Decl)}
    {ifaces : List (String × Interface)} (h : ProgramTranslation p outs ifaces)
    (hnd : (p.map (·.1)).Nodup) (key : DeclRef) (args : List (Val N)) (fuel : Nat)
    (r : Except (Val N) (Val N)) (hr : IR.callIn (IR.functionsOf outs) key args fuel = some r) :
    Eval.callIn p key args fuel = some r :=
  calls_agree p (IR.functionsOf outs) (programTranslation_rel h p hnd fun _ _ h => h).2.2.2.2.2
    (fuel + 1) key args r hr

/-- The same, for a call that returns: a call of a function of the output
gives a value only when the interpreter gives the same value for the same
call of the program. -/
theorem program_sound {p : Eval.Program} {outs : List (String × List IR.Decl)}
    {ifaces : List (String × Interface)} (h : ProgramTranslation p outs ifaces)
    (hnd : (p.map (·.1)).Nodup) (key : DeclRef) (args : List (Val N)) (fuel : Nat) (v : Val N)
    (hv : IR.runIn (IR.functionsOf outs) key args fuel = some v) :
    Eval.runIn p key args fuel = some v := by
  simp only [IR.runIn, Eval.runIn, bind_toOption] at hv ⊢
  exact program_sound_call h hnd key args fuel _ hv

/-- The same, for one file: when `translateTree` parses the file to the module
`m` and translates it to `decls`, a call of a function of `decls` returns or
throws a value only when the same call of `m` returns or throws the same value
in the interpreter. -/
theorem translate_sound_call {file source : String} {target : Edition} {m : Module} {names : IR.Names}
    {decls : List IR.Decl} (h : translateTree file source target = .ok (m, names, decls))
    (name : String) (args : List (Val N)) (fuel : Nat) (v : Except (Val N) (Val N))
    (hv : IR.callIn (IR.functionsOf [(file, decls)]) ⟨file, name⟩ args fuel = some v) :
    Eval.callIn [(file, m)] ⟨file, name⟩ args fuel = some v := by
  unfold translateTree translateFile at h
  cases hp : parse source target with
  | error e => simp [hp, Except.mapError] at h; cases h
  | ok m' =>
    simp only [hp, Except.mapError, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r heq
      split at heq
      · cases heq
      · rename_i decls' ctx' hrun
        simp only [pure, Except.pure, Except.ok.injEq] at heq
        subst heq
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        exact program_sound_call (.snoc false "N" .nil rfl rfl rfl hrun) (by simp) _ args fuel v hv

/-- The same, for one file and a call that returns: a call of a function of
`decls` gives a value only when the interpreter gives the same value for the
same call of `m`. -/
theorem translate_sound {file source : String} {target : Edition} {m : Module} {names : IR.Names}
    {decls : List IR.Decl} (h : translateTree file source target = .ok (m, names, decls))
    (name : String) (args : List (Val N)) (fuel : Nat) (v : Val N)
    (hv : IR.runIn (IR.functionsOf [(file, decls)]) ⟨file, name⟩ args fuel = some v) :
    Eval.runIn [(file, m)] ⟨file, name⟩ args fuel = some v := by
  simp only [IR.runIn, Eval.runIn, bind_toOption] at hv ⊢
  exact translate_sound_call h name args fuel _ hv

end tolean.TypeScript.Proof
