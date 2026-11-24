import tolean.Experimental.LoopCore.Examples

open tolean.Experimental.LoopCore
open Examples

def main : IO Unit := do
  let cases : List (String × Except String C.Body) := [
    ("sum_c", C.translateChecked head sumBody (.value (.var "s"))),
    ("find_c", C.translateChecked head findBody (.value (.int (-1)))),
    ("clamp_sum_c", C.translateChecked head clampBody (.value (.var "s"))),
    ("sum_cpp", Cpp.translateChecked range rangeSum (.value (.var "s"))),
    ("find_cpp", Cpp.translateChecked valueRange rangeFind (.value (.int (-1)))),
    ("index_cpp", Cpp.translateChecked range indexedRangeElement (.value (.int 0))),
    ("two_loops_cpp", do
      let rest ← Cpp.translateChecked valueRange second (.value (.var "s"))
      Cpp.translateChecked range rangeSum rest),
    ("repeated_c", C.translateChecked head repeatedWrite (.value (.var "s"))),
    ("repeated_cpp", Cpp.translateChecked range repeatedWrite (.value (.var "s"))),
    ("branches_c", C.translateChecked head branchWrite (.value (.var "s"))),
    ("branches_cpp", Cpp.translateChecked range branchWrite (.value (.var "s")))]
  for (name, result) in cases do
    match result with
    | .error message => throw (IO.userError s!"{name}: {message}")
    | .ok body =>
      IO.println s!"--- {name}.lean"
      IO.print (golden name body)
