import tolean.Prototype.LoopCore.Examples

open tolean.Prototype.LoopCore.Examples

def main : IO Unit := do
  for (name, body) in [("sum_c", sumIR), ("find_c", findIR), ("clamp_sum_c", clampIR),
      ("sum_cpp", cppSumIR), ("find_cpp", cppFindIR), ("two_loops_cpp", twoIR)] do
    IO.println s!"--- {name}.lean"
    IO.print (golden name body)
