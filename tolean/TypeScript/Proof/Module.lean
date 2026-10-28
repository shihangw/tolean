import tolean.TypeScript.Proof.Stmt

/-!
The translator is sound: a translated program computes only what the
TypeScript program computes.

`program_sound` states it for a program of several files, and
`translate_sound` for one file. When the translator translates every file of
a program, each file after the files it imports from, and a function of the
output gives a value for some arguments in the output's evaluator, then the
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

The theorem is about the output tree. The printer link is trusted: that the
printed Lean computes what the output's evaluator gives.
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
    simp only [pure_ok] at h
    refine ⟨h.2.symm, fun f hf heq => hn ?_⟩
    simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact Or.inr ⟨f, hf, heq⟩

end State

/-- The functions that a declaration adds, as references: a function adds
itself, and an import adds each name that it imports as a value. -/
def declRefs (file : String) : Decl → List DeclRef
  | .function _ _ name _ _ _ => [⟨file, name⟩]
  | .import _ names source =>
    match Eval.resolvePath file source with
    | some target => (names.filter (!·.typeOnly)).map fun n => ⟨target, n.name⟩
    | none => []
  | _ => []

/-- The interfaces name the files they come from. -/
def IfacesSelf (ifaces : List (String × Interface)) : Prop :=
  ∀ t i, ifaces.lookup t = some i → ∀ g ∈ i.functions, g.file = t

theorem params_fold {α : Type}
    {g : Env × List (String × α) × List Ty → Param → TM (Env × List (String × α) × List Ty)}
    (hstep : ∀ env lp ts p ctx r ctx', g (env, lp, ts) p ctx = .ok r ctx' →
      (∀ x, r.1.has x = (env.has x || x == p.name)) ∧ r.1.functions = env.functions ∧
        ∃ t, r.2.1 = lp ++ [(p.name, t)]) :
    ∀ (ps : List Param) (env : Env) lp ts ctx r ctx', ps.foldlM g (env, lp, ts) ctx = .ok r ctx' →
      (∀ x, r.1.has x = (env.has x || decide (x ∈ ps.map (·.name)))) ∧ r.1.functions = env.functions ∧
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

/-- What a function declaration does: it adds itself to the functions, and its
body is the translation of the source body, in a scope of its parameters and
of the functions declared before it. -/
theorem translateFunction_ok {sp : Span} {ex : Bool} {name : String} {params : List Param}
    {ret : Option TypeExpr} {body : Stmt} {s s' : Ctx} {o : Output.Decl}
    (h : translateFunction sp ex name params ret body s = .ok o s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧
      (∀ g ∈ s.functions, g.name ≠ name) ∧
      ∃ f, s'.functions = s.functions ++ [f] ∧ f.file = s.file ∧ f.name = name ∧ f.exported = ex ∧
      ∃ lp r out, o = .function name lp r out ∧ lp.map (·.1) = params.map (·.name) ∧
        ∃ F env c c', translateStatements F env .ret (blockStatements body) c = .ok out c' ∧
          env.functions = s.functions ∧ ∀ x, env.has x = decide (x ∈ params.map (·.name)) := by
  unfold translateFunction at h
  cases ret with
  | none => simp at h
  | some returnType =>
    simp only [bind_ok] at h
    obtain ⟨name', s₁, hname, u, s₂, htop, c, s₃, hget, ⟨env, lp, ts⟩, s₄, hfold, h⟩ := h
    obtain ⟨rfl, rfl⟩ := checkName_ok hname
    obtain ⟨rfl, hfresh⟩ := declareTopLevel_ok htop
    simp only [get_ok] at hget
    obtain ⟨rfl, rfl⟩ := hget
    obtain ⟨rfl, s₅, hfold⟩ := isolated_ok hfold
    have hps := params_fold (hstep := fun env lp ts p ctx r ctx' hg => by
        simp only [bind_ok, orReject_ok, ite_state] at hg
        obtain ⟨type, s₁, ⟨-, rfl⟩, pn, s₂, hpn, hg⟩ := hg
        obtain ⟨rfl, -⟩ := checkName_ok hpn
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
    simp only [modify_ok, fuelLimit_ok, pure_ok] at h
    obtain ⟨r, s₆, hr, _, s₇, rfl, _, _, ⟨rfl, rfl⟩, out, s₈, hbody, _, s₉, rfl, rfl, rfl⟩ := h
    obtain ⟨rfl, -⟩ := isolated_ok hr
    obtain ⟨rfl, s₁₀, hbody⟩ := isolated_ok hbody
    refine ⟨rfl, rfl, hfresh, _, rfl, rfl, rfl, rfl, lp, r.lean, out, rfl, ?_, _, env, _, _, hbody,
      hps.2.1, fun x => ?_⟩
    · simpa using hps.2.2
    · rw [hps.1 x]; simp [Env.has, Env.lookup]

/-- What an import does: it adds each name that it imports as a value, from the
file it names, and keeps the function names distinct. -/
theorem translateImport_ok {sp : Span} {names : List ImportName} {source : String} {s s' : Ctx}
    {u : Unit} (hself : IfacesSelf s.interfaces) (h : translateImport sp names source s = .ok u s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧
      ∃ more, s'.functions = s.functions ++ more ∧
        more.map FnInfo.ref = declRefs s.file (.import sp names source) ∧
        (∀ f ∈ more, f.exported = false) ∧
        ((s.functions.map (·.name)).Nodup → (s'.functions.map (·.name)).Nodup) ∧
        (∀ f ∈ more, ∃ i, s.interfaces.lookup f.file = some i ∧ ∃ g ∈ i.functions, g.name = f.name) := by
  unfold translateImport at h
  simp only [bind_ok, get_ok, orReject_ok] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, target, s₂, ⟨htarget, rfl⟩, iface, s₃, ⟨hiface, rfl⟩, hloop⟩ := h
  have hgf := hself _ _ hiface
  simp only [declRefs, htarget]
  suffices key : s'.file = s₁.file ∧ s'.interfaces = s₁.interfaces ∧
      ∃ more, s'.functions = s₁.functions ++ more ∧
        more.map FnInfo.ref = (names.filter (!·.typeOnly)).map (fun n => (⟨target, n.name⟩ : DeclRef)) ∧
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
    · -- An interface: the functions do not change.
      rename_i htype
      simp only [bind_ok, orReject_ok, modify_ok] at hstep
      obtain ⟨info, s₆, ⟨-, rfl⟩, rfl⟩ := hstep
      obtain ⟨hf, hi, more, hfns, hrefs, hex, hnd, horig⟩ := ih _ hloop
      refine ⟨hf, hi, more, hfns, ?_, hex, hnd, horig⟩
      simp [htype, hrefs]
    · rename_i htype
      try simp only [ite_state] at hstep
      split at hstep
      · simp at hstep
      · simp only [pure_bind, bind_ok, orReject_ok, modify_ok] at hstep
        obtain ⟨fn, s₆, ⟨hfind, rfl⟩, rfl⟩ := hstep
        obtain ⟨hf, hi, more, hfns, hrefs, hex, hnd, horig⟩ := ih _ hloop
        have hname : fn.name = n.name := by simpa using List.find?_some hfind
        have hfile := hgf fn (List.mem_of_find?_eq_some hfind)
        refine ⟨hf, hi, { fn with exported := false } :: more, by simpa using hfns, ?_, ?_, ?_, ?_⟩
        · simp [htype, hrefs, FnInfo.ref, hname, hfile]
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

theorem translateInterface_ok {sp : Span} {ex : Bool} {name : String} {fields : List Field}
    {s s' : Ctx} {o : Output.Decl} (h : translateInterface sp ex name fields s = .ok o s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧ s'.functions = s.functions ∧
      ∃ n fs, o = .struct n fs := by
  unfold translateInterface at h
  simp only [bind_ok, modify_ok, pure_ok] at h
  obtain ⟨name', s₁, hname, u, s₂, htop, infos, s₃, hinfos, _, s₄, rfl, rfl, rfl⟩ := h
  obtain ⟨rfl, rfl⟩ := checkName_ok hname
  obtain ⟨rfl, -⟩ := declareTopLevel_ok htop
  obtain ⟨rfl, -⟩ := isolated_ok hinfos
  exact ⟨rfl, rfl, rfl, _, _, rfl⟩

/-- What one declaration does to the state: it keeps the file and the
interfaces, adds its functions at the end, and keeps their names distinct. A
function that it adds as exported is one that it declares as exported. -/
theorem translateDecl_ok {d : Decl} {s s' : Ctx} {o : Option Output.Decl}
    (hself : IfacesSelf s.interfaces) (h : translateDecl d s = .ok o s') :
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧
      ∃ more, s'.functions = s.functions ++ more ∧ more.map FnInfo.ref = declRefs s.file d ∧
        ((s.functions.map (·.name)).Nodup → (s'.functions.map (·.name)).Nodup) ∧
        (∀ f ∈ more, f.exported = true → ∃ sp ps r b, d = .function sp true f.name ps r b) ∧
        (∀ f ∈ more, (f.file = s.file ∧ ∃ sp ex ps r b, d = .function sp ex f.name ps r b) ∨
          ∃ i, s.interfaces.lookup f.file = some i ∧ ∃ g ∈ i.functions, g.name = f.name) := by
  cases d with
  | «import» sp names source =>
    simp only [translateDecl, bind_ok, pure_ok] at h
    obtain ⟨u, s₁, h₁, rfl, rfl⟩ := h
    obtain ⟨hf, hi, more, hfns, hrefs, hex, hnd, horig⟩ := translateImport_ok hself h₁
    exact ⟨hf, hi, more, hfns, hrefs, hnd, fun f hf' he => by simp [hex f hf'] at he,
      fun f hf' => .inr (horig f hf')⟩
  | interface sp ex name fields =>
    simp only [translateDecl, map_ok] at h
    obtain ⟨o', h₁, rfl⟩ := h
    obtain ⟨hf, hi, hfns, -⟩ := translateInterface_ok h₁
    exact ⟨hf, hi, [], by simp [hfns], by simp [declRefs], by simp [hfns], by simp, by simp⟩
  | function sp ex name params ret body =>
    simp only [translateDecl, map_ok] at h
    obtain ⟨o', h₁, rfl⟩ := h
    obtain ⟨hf, hi, hfresh, f, hfns, hfile, hname, hex, -⟩ := translateFunction_ok h₁
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
      exact ⟨sp, params, ret, body, by rw [hname]⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact .inl ⟨hfile, sp, ex, params, ret, body, by rw [hname]⟩
  | typeAlias sp ex name type => simp [translateDecl] at h
  | exportedVar sp decl => simp [translateDecl] at h
  | stmt st => simp [translateDecl] at h

/-- `R` holds for each pair of elements in the same place. -/
def Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Forall₂ R as bs
  | _, _ => False

/-- The output function `out` is the translation of the source function
`src`: the same name, the same parameters, and a body that the translator made
from the source body, in a scope of exactly the parameters and of functions
of `F`. -/
def FnRelIn (F : List FnInfo) (src : String × List String × Stmt)
    (out : String × List String × Output.Body) : Prop :=
  src.1 = out.1 ∧ src.2.1 = out.2.1 ∧
    ∃ Fu env c c', translateStatements Fu env .ret (blockStatements src.2.2) c = .ok out.2.2 c' ∧
      (∀ g ∈ env.functions, g ∈ F) ∧ ∀ x, env.has x = decide (x ∈ src.2.1)

theorem Forall₂.mono {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, Forall₂ R l₁ l₂ → Forall₂ S l₁ l₂
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hab, hr⟩ => ⟨h _ _ hab, Forall₂.mono h hr⟩
  | [], _ :: _, h' | _ :: _, [], h' => h'.elim

theorem FnRelIn.mono {F G : List FnInfo} (hFG : ∀ g ∈ F, g ∈ G) {src out}
    (h : FnRelIn F src out) : FnRelIn G src out := by
  obtain ⟨h1, h2, Fu, env, c, c', ht, hf, hh⟩ := h
  exact ⟨h1, h2, Fu, env, c, c', ht, fun g hg => hFG g (hf g hg), hh⟩

/-- What a list of declarations does to the state, and how its functions
translate. -/
theorem decls_ok : ∀ (ds : List Decl) (s s' : Ctx) (os : List (Option Output.Decl)),
    IfacesSelf s.interfaces → ds.mapM translateDecl s = .ok os s' →
    s'.file = s.file ∧ s'.interfaces = s.interfaces ∧
      (∃ more, s'.functions = s.functions ++ more ∧ more.map FnInfo.ref = ds.flatMap (declRefs s.file) ∧
        (∀ f ∈ more, f.exported = true → ∃ sp ps r b, Decl.function sp true f.name ps r b ∈ ds) ∧
        ∀ f ∈ more, (f.file = s.file ∧ ∃ sp ex ps r b, Decl.function sp ex f.name ps r b ∈ ds) ∨
          ∃ i, s.interfaces.lookup f.file = some i ∧ ∃ g ∈ i.functions, g.name = f.name) ∧
      ((s.functions.map (·.name)).Nodup → (s'.functions.map (·.name)).Nodup) ∧
      Forall₂ (FnRelIn s'.functions) (Eval.functions ⟨ds⟩) (Output.functions (os.filterMap id))
  | [], s, s', os, _, h => by
    simp only [List.mapM_nil, pure_ok] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, ⟨[], by simp, by simp, by simp, by simp⟩, id,
      by simp [Eval.functions, Output.functions]; trivial⟩
  | d :: ds, s, s', os, hself, h => by
    simp only [List.mapM_cons, bind_ok, pure_ok] at h
    obtain ⟨o, s₁, h₁, os', s₂, h₂, rfl, rfl⟩ := h
    obtain ⟨hf₁, hi₁, more₁, hfns₁, hrefs₁, hnd₁, hex₁, hor₁⟩ := translateDecl_ok hself h₁
    obtain ⟨hf₂, hi₂, ⟨more₂, hfns₂, hrefs₂, hex₂, hor₂⟩, hnd₂, hrel⟩ :=
      decls_ok ds s₁ s₂ os' (by rw [hi₁]; exact hself) h₂
    refine ⟨hf₂.trans hf₁, hi₂.trans hi₁, ⟨more₁ ++ more₂, by rw [hfns₂, hfns₁, List.append_assoc],
      by rw [List.map_append, hrefs₁, hrefs₂, hf₁, List.flatMap_cons], ?_, ?_⟩, fun h => hnd₂ (hnd₁ h), ?_⟩
    · intro f hf he
      rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨sp, ps, r, b, hd⟩ := hex₁ f hf he
        exact ⟨sp, ps, r, b, by rw [hd]; exact List.mem_cons_self ..⟩
      · obtain ⟨sp, ps, r, b, hd⟩ := hex₂ f hf he
        exact ⟨sp, ps, r, b, List.mem_cons_of_mem _ hd⟩
    · intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · rcases hor₁ f hf with ⟨hfl, sp, ex, ps, r, b, hd⟩ | h
        · exact .inl ⟨hfl, sp, ex, ps, r, b, by rw [hd]; exact List.mem_cons_self ..⟩
        · exact .inr h
      · rcases hor₂ f hf with ⟨hfl, sp, ex, ps, r, b, hd⟩ | h
        · exact .inl ⟨hfl.trans hf₁, sp, ex, ps, r, b, List.mem_cons_of_mem _ hd⟩
        · exact .inr (by rw [← hi₁]; exact h)
    · -- The functions of the head, then the rest.
      have hsub : ∀ g ∈ s₁.functions, g ∈ s₂.functions := fun g hg => by
        rw [hfns₂]; exact List.mem_append_left _ hg
      cases d with
      | function sp ex name params ret body =>
        simp only [translateDecl, map_ok] at h₁
        obtain ⟨o', h₁, rfl⟩ := h₁
        obtain ⟨-, -, -, f, hfns, -, -, -, lp, r, out, rfl, hlp, Fu, env, c, c', ht, henv, hhas⟩ :=
          translateFunction_ok h₁
        simp only [Eval.functions, Output.functions, List.filterMap_cons] at hrel ⊢
        refine ⟨⟨rfl, hlp.symm, Fu, env, c, c', ht, fun g hg => ?_, hhas⟩, hrel⟩
        rw [henv] at hg
        exact hsub g (by rw [hfns]; exact List.mem_append_left _ hg)
      | «import» sp names source =>
        simp only [translateDecl, bind_ok, pure_ok] at h₁
        obtain ⟨u, s₃, -, rfl, -⟩ := h₁
        simpa [Eval.functions, Output.functions, List.filterMap_cons] using hrel
      | interface sp ex name fields =>
        simp only [translateDecl, map_ok] at h₁
        obtain ⟨o', h₁, rfl⟩ := h₁
        obtain ⟨-, -, -, n, fs, rfl⟩ := translateInterface_ok h₁
        simpa [Eval.functions, Output.functions, List.filterMap_cons] using hrel
      | typeAlias sp ex name type => simp [translateDecl] at h₁
      | exportedVar sp decl => simp [translateDecl] at h₁
      | stmt st => simp [translateDecl] at h₁

theorem nodup_map_eq {α β : Type} [DecidableEq β] {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b
  | [], _, a, ha, _, _, _ => by simp at ha
  | x :: xs, h, a, ha, b, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    obtain ⟨hx, hxs⟩ := h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · exact absurd hab.symm (hx b hb)
    · rcases hb with rfl | hb
      · exact absurd hab (hx a ha)
      · exact nodup_map_eq hxs a ha b hb hab

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

/-- Every function that a file's translation knows is the one that a call of its
name runs in that file. -/
theorem module_resolves {p : Eval.Program} {file : String} {m : Module} (hp : p.lookup file = some m)
    {ifaces : List (String × Interface)} (hfaith : Faithful p ifaces) {F : List FnInfo}
    (hrefs : F.map FnInfo.ref = m.decls.flatMap (declRefs file)) (hnd : (F.map (·.name)).Nodup)
    (horig : ∀ f ∈ F, (f.file = file ∧ ∃ sp ex ps r b, Decl.function sp ex f.name ps r b ∈ m.decls) ∨
      ∃ i, ifaces.lookup f.file = some i ∧ ∃ g ∈ i.functions, g.name = f.name) :
    ∀ f ∈ F, Eval.resolve ⟨p, file⟩ f.name = some f.ref := by
  intro f hf
  -- Two functions of `F` with one name are one function.
  have huniq : ∀ g ∈ F, g.name = f.name → g = f := fun g hg hn => nodup_map_eq hnd g hg f hf hn
  have hmem : ∀ r ∈ m.decls.flatMap (declRefs file), ∃ g ∈ F, g.ref = r := by
    intro r hr
    rw [← hrefs] at hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
    exact ⟨g, hg, rfl⟩
  have hown_iff : ((Eval.functions m).any fun x => x.fst == f.name) = true ↔
      ∃ sp ex ps r b, Decl.function sp ex f.name ps r b ∈ m.decls := by
    simp only [List.any_eq_true, beq_iff_eq, Eval.functions, List.mem_filterMap]
    constructor
    · rintro ⟨⟨n, ps, b⟩, ⟨d, hd, hsel⟩, rfl⟩
      cases d <;> simp at hsel
      obtain ⟨rfl, -, rfl⟩ := hsel
      exact ⟨_, _, _, _, _, hd⟩
    · rintro ⟨sp, ex, ps, r, b, hd⟩
      exact ⟨(f.name, ps.map (·.name), b), ⟨_, hd, rfl⟩, rfl⟩
  unfold Eval.resolve
  simp only [hp, Option.bind_eq_bind, Option.bind_some]
  by_cases hown : ((Eval.functions m).any fun x => x.fst == f.name) = true
  · rw [if_pos hown]
    obtain ⟨sp, ex, ps, r, b, hd⟩ := hown_iff.mp hown
    obtain ⟨g, hg, hgr⟩ := hmem ⟨file, f.name⟩ (List.mem_flatMap.mpr ⟨_, hd, by simp [declRefs]⟩)
    have hgf := huniq g hg (by simpa [FnInfo.ref] using congrArg DeclRef.name hgr)
    subst hgf
    rw [hgr]; rfl
  · rw [if_neg hown]
    have hnot : ¬ ∃ sp ex ps r b, Decl.function sp ex f.name ps r b ∈ m.decls :=
      fun h => hown (hown_iff.mpr h)
    obtain ⟨i, hi, g, hg, hgn⟩ := (horig f hf).resolve_left fun h => hnot h.2
    obtain ⟨tm, htm, hexp⟩ := hfaith _ _ hi g hg
    rw [hgn] at hexp
    rw [findSome_eq (l := m.decls) (x := f.file) ?ex ?uniq]
    · simp only [Option.bind_some, htm, hexp, if_true]
      rfl
    case ex =>
      have hr : f.ref ∈ m.decls.flatMap (declRefs file) := by
        rw [← hrefs]; exact List.mem_map_of_mem hf
      obtain ⟨d, hd, hrd⟩ := List.mem_flatMap.mp hr
      cases d with
      | function sp ex name ps r b =>
        simp only [declRefs, List.mem_singleton, FnInfo.ref, DeclRef.mk.injEq] at hrd
        exact absurd ⟨sp, ex, ps, r, b, hrd.2 ▸ hd⟩ hnot
      | «import» sp names source =>
        refine ⟨_, hd, ?_⟩
        simp only [declRefs] at hrd
        split at hrd
        · rename_i target htarget
          obtain ⟨n, hn, hnr⟩ := List.mem_map.mp hrd
          simp only [List.mem_filter] at hn
          simp only [FnInfo.ref, DeclRef.mk.injEq] at hnr
          have hany : (names.any fun n => !n.typeOnly && n.name == f.name) = true :=
            List.any_eq_true.mpr ⟨n, hn.1, by simpa [hnr.2] using hn.2⟩
          simp [hany, htarget]
        · simp at hrd
      | _ => simp [declRefs] at hrd
    case uniq =>
      intro d hd y hy
      cases d with
      | «import» sp names source =>
        simp only at hy
        split at hy
        · rename_i hany
          obtain ⟨n, hn, hnn⟩ := List.any_eq_true.mp hany
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hnn
          have hr : (⟨y, f.name⟩ : DeclRef) ∈ m.decls.flatMap (declRefs file) := by
            refine List.mem_flatMap.mpr ⟨_, hd, ?_⟩
            simp only [declRefs, hy]
            exact List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨hn, by simp [hnn.1]⟩, by rw [hnn.2]⟩
          obtain ⟨g', hg', hgr⟩ := hmem _ hr
          have := huniq g' hg' (by simpa [FnInfo.ref] using congrArg DeclRef.name hgr)
          subst this
          simpa [FnInfo.ref] using (congrArg DeclRef.file hgr).symm
        · simp at hy
      | _ => simp at hy

/-! ### Programs -/

/-- The output function `out` is the translation of the source function `src`
of a program: the same key, the same parameters, and a body that the
translator made from the source body. Its scope binds exactly the parameters,
and each function it may call is the one that a call of that name runs in its
file. -/
def FnRelP (p : Eval.Program) (src : DeclRef × List String × Stmt)
    (out : DeclRef × List String × Output.Body) : Prop :=
  src.1 = out.1 ∧ src.2.1 = out.2.1 ∧
    ∃ Fu env c c', translateStatements Fu env .ret (blockStatements src.2.2) c = .ok out.2.2 c' ∧
      Resolves ⟨p, src.1.file⟩ env ∧ ∀ x, env.has x = decide (x ∈ src.2.1)

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
    ∀ {srcs : List (DeclRef × List String × Stmt)} {outs : List (DeclRef × List String × Output.Body)},
      Forall₂ (FnRelP p) srcs outs → ∀ {key : DeclRef} {ps : List String} {b : Output.Body},
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

variable (p : Eval.Program) (fs : List (DeclRef × List String × Output.Body))

/-- Every call of the output gives what the same call of the source gives,
for every fuel. -/
theorem calls_agree (hrel : Forall₂ (FnRelP p) (Eval.functionsOf p) fs) :
    ∀ fuel, CallsAgree (N := N) p fs fuel
  | 0 => fun key vs v h => by simp [callO] at h
  | fuel + 1 => fun key vs v h => by
    have hc := calls_agree hrel fuel
    simp only [callO] at h
    cases hl : fs.lookup key with
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
            obtain ⟨bS, hlS, -, -, F, env, ctx, ctx', htr, hres, henv⟩ := lookup_rel hrel hl
            have hlen' : ps.length = vs.length := by simpa using hlen
            have hsim := (stmts_sound ⟨p, key.file⟩ fs fuel hc F).1 _ _ _ _ _ _ htr
            have hex := (hsim _ _ (fun _ => rfl) (scoped_params henv hres hlen')).1 w hb
            have hst := block_ret ⟨p, key.file⟩ fuel bS hex
            simp [callS, hlS, hlen', hst]

end Calls

/-- The translation of a program, file by file. Each file's translation starts
with no functions and with the interfaces of the files before it. -/
inductive ProgramTranslation :
    Eval.Program → List (String × List Output.Decl) → List (String × Interface) → Prop
  | nil : ProgramTranslation [] [] []
  | snoc {p : Eval.Program} {outs : List (String × List Output.Decl)} {ifaces : List (String × Interface)}
      {file : String} {m : Module} {decls : List Output.Decl} {start finish : Ctx}
      (usesNumber : Bool) (numberVar : String) :
      ProgramTranslation p outs ifaces → start.file = file → start.functions = [] →
      start.interfaces = ifaces → translateDecls m start = .ok decls finish →
      ProgramTranslation (p ++ [(file, m)]) (outs ++ [(file, decls)])
        (ifaces ++ [(file, finish.interface usesNumber numberVar)])

theorem lookup_append_some {β : Type} {k : String} {b : β} :
    ∀ {l l' : List (String × β)}, l.lookup k = some b → (l ++ l').lookup k = some b
  | (k', v) :: l, l', h => by
    simp only [List.cons_append, List.lookup] at h ⊢
    split <;> simp_all [lookup_append_some]
  | [], _, h => by simp at h

theorem lookup_append_none {β : Type} {k : String} :
    ∀ {l l' : List (String × β)}, k ∉ l.map Prod.fst → (l ++ l').lookup k = l'.lookup k
  | [], _, _ => rfl
  | (k', v) :: l, l', h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have : (k == k') = false := beq_eq_false_iff_ne.mpr h.1
    simp only [List.cons_append, List.lookup, this]
    exact lookup_append_none h.2

theorem lookup_append_mem {β : Type} {k : String} :
    ∀ {l l' : List (String × β)}, k ∈ l.map Prod.fst → (l ++ l').lookup k = l.lookup k
  | [], _, h => by simp at h
  | (k', v) :: l, l', h => by
    simp only [List.cons_append, List.lookup]
    by_cases hk : k = k'
    · subst hk; simp
    · have : (k == k') = false := beq_eq_false_iff_ne.mpr hk
      simp only [this]
      simp only [List.map_cons, List.mem_cons, hk, false_or] at h
      exact lookup_append_mem h

/-- What a program's translation gives: interfaces that name their files and
that the program's files export, and output functions that are the
translations of the program's functions. -/
theorem programTranslation_rel {p : Eval.Program} {outs : List (String × List Output.Decl)}
    {ifaces : List (String × Interface)} (h : ProgramTranslation p outs ifaces) :
    ∀ (P : Eval.Program), (p.map (·.1)).Nodup → (∀ t tm, p.lookup t = some tm → P.lookup t = some tm) →
      ifaces.map (·.1) = p.map (·.1) ∧ outs.map (·.1) = p.map (·.1) ∧ IfacesSelf ifaces ∧ Faithful P ifaces ∧
        Forall₂ (FnRelP P) (Eval.functionsOf p) (Output.functionsOf outs) := by
  induction h with
  | nil => intro P _ _; exact ⟨rfl, rfl, fun _ _ h => by simp at h, fun _ _ h => by simp at h, trivial⟩
  | @snoc p outs ifaces file m decls start finish u nv hrest hfile hfns hifaces htr ih =>
    intro P hnd hP
    simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append, List.mem_singleton] at hnd
    have hnotin : file ∉ p.map (·.1) := fun h => hnd.2.2 _ h _ rfl rfl
    have hP' : ∀ t tm, p.lookup t = some tm → P.lookup t = some tm := fun t tm h =>
      hP t tm (lookup_append_some h)
    obtain ⟨hik, hok, hself, hfaith, hrel⟩ := ih P hnd.1 hP'
    have hPm : P.lookup file = some m := hP file m (by rw [lookup_append_none hnotin]; simp)
    -- The file's own translation.
    simp only [translateDecls, bind_ok, pure_ok] at htr
    obtain ⟨os, finish, hos, rfl, rfl⟩ := htr
    obtain ⟨hf, hi, ⟨more, hfns', hrefs, hex, horig⟩, hnd', hrelm⟩ :=
      decls_ok m.decls start finish os (by rw [hifaces]; exact hself) hos
    rw [hfns, List.nil_append] at hfns'
    have hres : ∀ f ∈ finish.functions, Eval.resolve ⟨P, file⟩ f.name = some f.ref := by
      rw [hfns']
      refine module_resolves hPm (ifaces := ifaces) hfaith (by rw [hrefs, hfile]) ?_ ?_
      · rw [← hfns']; exact hnd' (by rw [hfns]; simp)
      · intro f hf'
        rcases horig f hf' with ⟨hfl, hd⟩ | ⟨i, hi', hg⟩
        · exact .inl ⟨hfl.trans hfile, hd⟩
        · exact .inr ⟨i, by rw [← hifaces]; exact hi', hg⟩
    have hkeys : file ∉ ifaces.map (·.1) := by rw [hik]; exact hnotin
    refine ⟨by simp [hik], by simp [hok], ?_, ?_, ?_⟩
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
          rw [hg.2.2, hf, hfile]
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
          rw [hfns'] at hg
          obtain ⟨sp, ps, r, b, hd⟩ := hex g hg.1 hg.2.1
          refine ⟨m, hPm, ?_⟩
          simp only [Eval.exportsFunction, List.any_eq_true]
          exact ⟨_, hd, by simp⟩
        · simp at hti
    · simp only [Eval.functionsOf, Output.functionsOf, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      refine hrel.append (Forall₂.map ?_ hrelm)
      intro x y hxy
      obtain ⟨hn, hps, Fu, env, c, c', ht, hsub, hhas⟩ := hxy
      refine ⟨by simp [hn], hps, Fu, env, c, c', ht, fun g hg => hres g (hsub g hg), hhas⟩

variable {N : Type} [JSNumber N]

/-- The translator is sound for a program. When it translates every file of a
program, a call of a function of the output gives a value only when the
interpreter gives the same value for the same call of the program, for all
arguments and all fuel. -/
theorem program_sound {p : Eval.Program} {outs : List (String × List Output.Decl)}
    {ifaces : List (String × Interface)} (h : ProgramTranslation p outs ifaces)
    (hnd : (p.map (·.1)).Nodup) (key : DeclRef) (args : List (Val N)) (fuel : Nat) (v : Val N)
    (hv : Output.runIn (Output.functionsOf outs) key args fuel = some v) :
    Eval.runIn p key args fuel = some v :=
  calls_agree p (Output.functionsOf outs) (programTranslation_rel h p hnd fun _ _ h => h).2.2.2.2
    (fuel + 1) key args v hv

/-- The same, for one file: when `translateTree` parses the file to the module
`m` and translates it to `decls`, a call of a function of `decls` gives a
value only when the interpreter gives the same value for the same call of
`m`. -/
theorem translate_sound {file source : String} {target : Edition} {m : Module} {names : Output.Names}
    {decls : List Output.Decl} (h : translateTree file source target = .ok (m, names, decls))
    (name : String) (args : List (Val N)) (fuel : Nat) (v : Val N)
    (hv : Output.runIn (Output.functionsOf [(file, decls)]) ⟨file, name⟩ args fuel = some v) :
    Eval.runIn [(file, m)] ⟨file, name⟩ args fuel = some v := by
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
        exact program_sound (.snoc false "N" .nil rfl rfl rfl hrun) (by simp) _ args fuel v hv

end tolean.TypeScript.Proof
