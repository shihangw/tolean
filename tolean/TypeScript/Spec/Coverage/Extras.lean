import tolean.TypeScript.Syntax.Layout
import tolean.TypeScript.Proof.Expr
import tolean.Project

/-! # Extras

Checks for rules that come from Lean and the project, not from ECMA-262: how
Lean reads the names that the output writes, and which files the output of a
file may name or import. They have no section of ECMA-262, so the index in
`Spec/Coverage.lean` lists them among its extras.
-/
namespace tolean.TypeScript.Coverage

open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate tolean.TypeScript.Proof

/-! ### Extras: How Lean reads the output -/

/-- An accepted predicate returns a boolean, never the type that it names. -/
theorem checked_guard_boolean {env : Env} {params : List Param} {sp : tolean.Span}
    {name : String} {target : TypeExpr} {body : Stmt} {s s' : Ctx} {ty : Ty}
    (h : translateReturnType env params (.predicate sp name target) body s = .ok ty s') :
    ty = .boolean := by
  simp only [translateReturnType] at h
  cases hg : Eval.guardTest params (some (.predicate sp name target)) body with
  | none => simp [hg] at h
  | some g =>
    simp only [hg] at h
    cases ht : tagTestOf env (g.expr sp g.parameter) with
    | none => simp [ht] at h
    | some test =>
      simp only [ht, bind_ok] at h
      obtain ⟨t, c, _, h⟩ := h
      by_cases hb : test.isEq = true
      all_goals
        simp only [hb, Bool.false_eq_true, if_false, if_true] at h
        split at h
        · simp only [pure_bind, pure_ok] at h
          exact h.1.symm
        · simp at h

/-- A parameter or a local never has the name of an interface of its file,
which Lean, unlike TypeScript, would read as the local. -/
theorem checkLocalName_not_interface {sp : Span} {name r : String} {s s' : Ctx}
    (h : checkLocalName sp name false s = .ok r s') :
    ∀ i ∈ s.structs, i.file = s.file → i.name ≠ name := by
  simp only [checkLocalName, bind_ok, get_ok, ite_state] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, h⟩ := h
  split at h
  · simp at h
  · rename_i hg
    intro i hi hf hn
    exact hg (List.any_eq_true.mpr ⟨i, hi, by simp [hn, hf]⟩)

-- A path component that Lean does not read as a name is written in «».
#guard Project.nameSegment "Util" == "Util"
#guard Project.nameSegment "my-lib" == "«my-lib»"
#guard Project.nameSegment "end" == "«end»"
#guard Project.nameSegment "2d" == "«2d»"
#guard Project.namespaceOf "my-lib/Util.lean" == "«my-lib».Util"

-- A unit's Lean module starts at `moduleRoot`, as the Lean package names it.
-- An import, a certificate and the chain manifest once named the namespace.
#guard (Project.moduleOf "" "src/Sorting.lean" matches .ok "src.Sorting")
#guard (Project.moduleOf "src" "src/my-lib/Util.lean" matches .ok "«my-lib».Util")
#guard (Project.moduleOf "lib" "Base.lean" matches .error _)

-- The check before printing sees every declaration that the output names: a
-- call, and a structure in a type.
#guard IR.Decl.refs
    (.function "f" [("g", .struct ⟨"a.ts", "G"⟩)] .int (.value (.call ⟨"b.ts", "h"⟩ [])) : IR.Decl) ==
  [⟨"a.ts", "G"⟩, ⟨"b.ts", "h"⟩]

/-! ### Extras: Imports across editions -/

/-- A file imports only from a file translated for an edition no newer than
its own. -/
theorem translateImport_edition {sp : Span} {names : List ImportName} {source : String}
    {s s' : Ctx} {u : Unit} (h : translateImport sp names source s = .ok u s') :
    ∀ target i, Eval.resolvePath s.file source = some target → s.interfaces.lookup target = some i →
      i.target.year ≤ s.target.year := by
  unfold translateImport at h
  simp only [bind_ok, get_ok, orReject_ok] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, target, s₂, ⟨htarget, rfl⟩, iface, s₃, ⟨hiface, rfl⟩, h⟩ := h
  simp only [ite_state] at h
  split at h
  · simp at h
  · rename_i hyear
    intro t i ht hi
    rw [htarget] at ht
    cases ht
    rw [hiface] at hi
    cases hi
    omega

-- The project reads each file's imports for the file's own target.
#guard Project.Job.edition (.typescript (Lean.Json.mkObj [("target", "ES2019")]) "x.ts") == .es2019

/-! ### Extras: Config inheritance -/

-- Fail on a second read, so a missing cache fails the regression immediately
-- instead of expanding the shared ancestry exponentially.
private def checkedConfigReads (configs : List (String × Lean.Json)) :
    Except String (Lean.Json × List String) :=
  let read (path : String) : StateT (List String) (Except String) String := do
    if (← get).contains path then throw s!"{path}: read twice"
    modify (path :: ·)
    match configs.lookup path with
    | some config => return config.compress
    | none => throw s!"{path}: missing config"
  (ModuleResolution.loadOptions (configs.map (·.1)) read
    (configs.length + 1) [] "tsconfig.json").run []

-- Thirty-two levels of repeated bases used to expand into billions of reads.
-- Both spellings of each ancestor must use its resolved path as the cache key.
#guard
  let configs := ("tsconfig.json", Lean.Json.mkObj [("extends", "./c31.json")]) ::
    (List.range 32).map fun n =>
      (s!"c{n}.json", if n == 0 then
        Lean.Json.mkObj [("compilerOptions", Lean.Json.mkObj [("moduleResolution", "bundler")])]
      else
        Lean.Json.mkObj [("extends", .arr #[
          .str s!"./c{n - 1}.json", .str s!"./nested/../c{n - 1}.json"])])
  match checkedConfigReads configs with
  | .ok (options, reads) =>
    reads.length == configs.length &&
    (ModuleResolution.setting (some options) none matches .ok .bundler)
  | .error _ => false

-- A cached ancestor supplies its own options, not a previous child's options.
-- The right branch replaces the left branch, even when its base is cached.
#guard
  let configs := [
    ("tsconfig.json", Lean.Json.mkObj [("extends", .arr #["./left.json", "./right.json"])]),
    ("left.json", Lean.Json.mkObj [("extends", "./base.json"),
      ("compilerOptions", Lean.Json.mkObj [("moduleResolution", "node16")])]),
    ("right.json", Lean.Json.mkObj [("extends", "./nested/../base.json")]),
    ("base.json", Lean.Json.mkObj [
      ("compilerOptions", Lean.Json.mkObj [("moduleResolution", "bundler")])])]
  match checkedConfigReads configs with
  | .ok (options, reads) =>
    reads.length == 4 && (ModuleResolution.setting (some options) none matches .ok .bundler)
  | .error _ => false

-- An unfinished ancestor is not a cache hit. Normalize the back edge before
-- checking the active stack, and keep the cycle diagnostic.
#guard
  let configs := [
    ("tsconfig.json", Lean.Json.mkObj [("extends", "./base.json")]),
    ("base.json", Lean.Json.mkObj [("extends", "./nested/../tsconfig.json")])]
  match checkedConfigReads configs with
  | .error message =>
    message == "tsconfig.json: config extends cycle: tsconfig.json -> base.json -> tsconfig.json"
  | .ok _ => false

end tolean.TypeScript.Coverage

-- The lexer splits both forms into the same kinds. The observation must
-- retain the adjacency that TypeScript uses when it rescans the closing `>`.
#guard match tolean.TypeScript.Syntax.lex "f < A >= x",
    tolean.TypeScript.Syntax.lex "f < A > = x" with
  | .ok tight, .ok spaced =>
    let a := tight.toList
    let b := spaced.toList
    a.map (·.kind) == b.map (·.kind) &&
    a.map (·.newlineBefore) == b.map (·.newlineBefore) &&
    tolean.TypeScript.Syntax.observations a != tolean.TypeScript.Syntax.observations b
  | _, _ => false

-- A split between `>` and `=` must carry the right boundary into the prefix.
#guard match tolean.TypeScript.Syntax.lex "f < A >= x" with
  | .ok tokens =>
    let ts := tokens.toList
    let before := ts.take 4
    let suffix := ts.drop 4
    let boundary := tolean.TypeScript.Syntax.observationBoundary suffix none
    let expected := (tolean.TypeScript.Syntax.observations ts).take 4
    tolean.TypeScript.Syntax.observations before boundary == expected &&
    tolean.TypeScript.Syntax.observations before != expected
  | _ => false
