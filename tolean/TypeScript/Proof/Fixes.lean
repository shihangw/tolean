import tolean.TypeScript.Proof.Module
import tolean.Project

/-!
Each bug that a review of the translator found, as a theorem or a check, so
that a later change cannot bring it back unseen. CI builds this file with the
rest of the library: a theorem that stops holding, or a `#guard` that turns
false, fails the build.

A theorem states the rule itself, for every input. A `#guard` checks one
input, where the rule is about concrete strings or a printed name. Each bug
that a whole program shows best is a file in `tests/typescript/corpus/` as
well.
-/
namespace tolean.TypeScript.Proof

open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate
open tolean.TypeScript.Eval (Val)

/-! ### The interpreter -/

/-- `{ NaN }` reads the global `NaN` when no local hides it (ECMA-262
§13.2.5.5). The interpreter once looked the name up only among the locals, and
gave no value. -/
theorem shorthand_reads_global {N : Type} [JSNumber N] (m : Eval.Scope) (fuel : Nat) (sp : Span) :
    Eval.eval (N := N) m fuel [] (.object sp [.shorthand sp "NaN"]) =
      some (.obj [("NaN", .num JSNumber.nan)]) := by
  simp [Eval.eval, Eval.evalProps, List.lookup]

/-- `-Infinity` negates a local named `Infinity` as any value, a bigint too.
The interpreter once gave no value when the local held a bigint. -/
theorem neg_local_infinity {N : Type} [JSNumber N] (m : Eval.Scope) (fuel : Nat) (sp : Span) (i : Int) :
    Eval.eval (N := N) m fuel [("Infinity", .int i)] (.unary sp .neg (.ident sp "Infinity")) =
      some (.int (-i)) := by
  simp [Eval.eval, List.lookup]

-- A number literal whose digits are all zero is 0, however long its fraction.
-- The interpreter once refused a zero with more than 400 fraction digits.
#guard Eval.numberLiteral ("0." ++ "".pushn '0' 401) == some 0
#guard Eval.numberLiteral ("0." ++ "".pushn '0' 401 ++ "1") == none

/-! ### Sources, as Node reads them

An import names the `.ts` file itself by a relative path. Node reads the
source as a URL, so the translator and the interpreter refuse what Node would
read another way. -/

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

/-! ### The translator -/

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

/-- A local never has the name of a function that a call may name, or of a
global that the subset reads. In JS, the local is in its temporal dead zone
from the start of its block, so a use of the name before it throws. -/
theorem declare_not_callable {env env' : Translate.Env} {sp : Span} {name : String} {b : Binding}
    {t : Ty} {s s' : Ctx} (h : declare env sp name b t s = .ok env' s') :
    (∀ f ∈ env.functions, f.name ≠ name) ∧ name ≠ "NaN" ∧ name ≠ "Infinity" ∧ name ≠ "Number" := by
  simp only [declare, ite_state] at h
  split at h
  · simp at h
  · simp only [pure_bind, ite_state] at h
    split at h
    · simp at h
    · rename_i hg
      refine ⟨fun f hf hn => hg ?_, ?_, ?_, ?_⟩
      · simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
        exact Or.inl ⟨f, hf, hn⟩
      all_goals rintro rfl; simp [isNumberName] at hg

/-- A parameter or a local never has the name of an interface of its file,
which Lean, unlike TypeScript, would read as the local. -/
theorem checkLocalName_not_interface {sp : Span} {name r : String} {s s' : Ctx}
    (h : checkLocalName sp name s = .ok r s') :
    ∀ i ∈ s.structs, i.file = s.file → i.name ≠ name := by
  simp only [checkLocalName, bind_ok, get_ok, ite_state] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, h⟩ := h
  split at h
  · simp at h
  · rename_i hg
    intro i hi hf hn
    exact hg (List.any_eq_true.mpr ⟨i, hi, by simp [hn, hf]⟩)

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

/-! ### Names that the output writes -/

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
#guard Output.Decl.refs
    (.function "f" [("g", .struct ⟨"a.ts", "G"⟩)] .int (.value (.call ⟨"b.ts", "h"⟩ []))) ==
  [⟨"a.ts", "G"⟩, ⟨"b.ts", "h"⟩]

-- The project reads each file's imports for the file's own target.
#guard Project.Job.edition (.typescript (Lean.Json.mkObj [("target", "ES2019")]) "x.ts") == .es2019

end tolean.TypeScript.Proof
