import tolean.Prototype.LoopCore.Examples

def sum_cpp (xs : List Int) (key limit : Int) : Int :=
  let s : Int := 0
  match Id.run (forIn xs (none, s)
      (fun (x : Int) ((_, s) : Option Int × Int) =>
        let s := (s + x)
        ForInStep.yield (none, s))) with
  | (some r, _) => r
  | (none, s) =>
    s
