import tolean.TypeScript.Proof.Expr

/-! # §16 ECMAScript Language: Scripts and Modules {#sec-ecmascript-language-scripts-and-modules} -/
namespace tolean.TypeScript.Coverage

open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate tolean.TypeScript.Proof

/-! ### §16.2.1.6.4 InitializeEnvironment {#sec-source-text-module-record-initialize-environment}

A module binds each of its function declarations in the module's
environment, and the outer environment of that one is the global one. So a
function of the module hides a global of the same name. -/

/-- A function or an interface is never named `NaN`, `Infinity` or `Number`,
which would hide the global that the subset reads under that name. -/
theorem declareTopLevel_not_global {sp : Span} {name : String} {s s' : Ctx} {u : Unit}
    (h : declareTopLevel sp name s = .ok u s') :
    name ≠ "NaN" ∧ name ≠ "Infinity" ∧ name ≠ "Number" := by
  simp only [declareTopLevel, bind_ok, get_ok, ite_state] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, h⟩ := h
  split at h
  · simp at h
  · simp only [pure_bind, ite_state] at h
    split at h
    · simp at h
    · rename_i hg
      refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp [isNumberName] at hg

/-! ### §16.2.1.8 HostLoadImportedModule {#sec-HostLoadImportedModule}

ECMA-262 leaves it to the host to find the module that a specifier names.
The subset follows Node, where the specifier names the `.ts` file itself by a
relative path. Node reads the specifier as a URL, so the translator and the
interpreter refuse a specifier that Node would read another way. -/

/-- A source with `%`, `?`, `#` or `\` names no file: Node reads a percent
escape, a query, a fragment and a backslash otherwise. -/
theorem resolvePath_url {file source : String}
    (h : (source.any fun c => c == '%' || c == '?' || c == '#' || c == '\\') = true) :
    Eval.resolvePath file source = none := by
  simp [Eval.resolvePath, h]

/-- A source that does not start with `./` or `../` names no file. -/
theorem resolvePath_relative {file source : String}
    (h₁ : (source.splitOn "/").head? ≠ some ".") (h₂ : (source.splitOn "/").head? ≠ some "..") :
    Eval.resolvePath file source = none := by
  unfold Eval.resolvePath
  split
  · rfl
  · simp [h₁, h₂]

/-- A source whose last segment is not a `.ts` file's name names no file, such
as `"./b.js"`, `"./b"` and `"./b.ts/."`, which names a directory in Node. -/
theorem resolvePath_last {file source raw : String} (hraw : (source.splitOn "/").getLast? = some raw)
    (h : raw.endsWith ".ts" = false ∨ raw = ".ts") :
    Eval.resolvePath file source = none := by
  rcases h with h | h
  · simp [Eval.resolvePath, hraw, h]
  · subst h
    simp [Eval.resolvePath, hraw]

#guard Eval.resolvePath "a/b.ts" "./c.ts" == some "a/c.ts"
#guard Eval.resolvePath "a/b.ts" "../c.ts" == some "c.ts"
#guard Eval.resolvePath "a/b.ts" "../../c.ts" == none
-- The importing file's own path is normalized first.
#guard Eval.resolvePath "a/./b.ts" "./c.ts" == some "a/c.ts"
#guard Eval.resolvePath "./x.ts" "../y.ts" == none
#guard Eval.resolvePath "x.ts" "./y.js" == none
#guard Eval.resolvePath "x.ts" "./y" == none
#guard Eval.resolvePath "x.ts" "./y.ts/." == none
#guard Eval.resolvePath "x.ts" "./y.ts?v=1" == none
#guard Eval.resolvePath "x.ts" "./y.ts#a" == none
#guard Eval.resolvePath "x.ts" "./y%2Ets" == none
#guard Eval.resolvePath "x.ts" "./sub\\y.ts" == none
#guard Eval.resolvePath "x.ts" "y.ts" == none

end tolean.TypeScript.Coverage
