import tolean.TypeScript.Proof.Module

namespace tolean.TypeScript.Translate.Proof
open Syntax

theorem forwardedFunctions_mem {c : Ctx} {m : Module} {g : FnInfo}
    (h : g ∈ c.forwardedFunctions m) :
    Eval.exportsFunction m g.name = false ∧
    ∃ target iface, Eval.exportSource? c.file m g.name = some target ∧
      c.interfaces.lookup target = some iface ∧ g ∈ iface.functions := by
  simp only [Ctx.forwardedFunctions, Ctx.forwardedValues, List.mem_filterMap] at h
  obtain ⟨n, _, h⟩ := h
  split at h
  · contradiction
  · rename_i hn
    have hn : n.typeOnly = false ∧ Eval.exportsFunction m n.name = false := by
      simpa using hn
    cases ht : Eval.exportSource? c.file m n.name with
    | none => simp [ht] at h
    | some target =>
      cases hi : c.interfaces.lookup target with
      | none => simp [ht, hi] at h
      | some iface =>
        simp only [ht, hi, Option.bind_eq_bind, Option.bind_some] at h
        have hg := List.mem_of_find?_eq_some h
        have he := List.find?_some h
        have hname : g.name = n.name := by simpa using he
        exact ⟨by simpa [hname] using hn.2, target, iface, by simpa [hname] using ht, hi, hg⟩

end tolean.TypeScript.Translate.Proof
