import Out
import tolean.TypeScript.Proof.Link

namespace ProjectProof

theorem squares : Out.«sort obligation at 2:10» := by
  unfold Out.«sort obligation at 2:10»
  intro N _ _ xs
  exact tolean.TypeScript.Proof.consistentOn_of_transCmp
    (compareOn (fun (a : Int) => a * a)) (by sort_tac)

theorem wrong : True := True.intro

end ProjectProof
