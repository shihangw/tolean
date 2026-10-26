/-
`#audit_claims Spec Proof` keeps what is claimed apart from how it is proved.

A claim is a `def` of type `Prop` in namespace `Spec`. The command fails the
build unless each claim has a theorem with the same name in `Proof` whose
type is exactly that claim, and unless `Spec` states at least one claim. A
reviewer then reads only the `Spec` file to know what is guaranteed.
-/
import Lean

namespace tolean
open Lean Elab Command

elab "#audit_claims " spec:ident proof:ident : command => do
  let env ← getEnv
  let specNs := spec.getId
  let proofNs := proof.getId
  let claims := env.constants.fold (init := #[]) fun found name info =>
    match info with
    | .defnInfo d =>
      if specNs.isPrefixOf name && !name.isInternal && d.type.isProp then found.push name
      else found
    | _ => found
  if claims.isEmpty then
    throwError "{specNs} states no claims"
  for claim in claims do
    let proved := claim.replacePrefix specNs proofNs
    match env.find? proved with
    | some (.thmInfo t) =>
      unless t.type == .const claim [] do
        throwError "{proved} must have type {claim} exactly, not{indentExpr t.type}"
    | _ => throwError "claim {claim} has no theorem {proved}"

end tolean
