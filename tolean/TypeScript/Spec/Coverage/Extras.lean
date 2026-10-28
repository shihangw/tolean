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

end tolean.TypeScript.Coverage
