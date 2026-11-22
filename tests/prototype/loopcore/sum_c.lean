import tolean.Prototype.LoopCore.Examples

def sum_c (xs : List Int) (key limit : Int) : Int :=
  let s : Int := 0
  match Id.run (forIn (tolean.Prototype.LoopCore.C.count (0 : Int) (4 : Int)) (none, s)
      (fun (i : Int) ((_, s) : Option Int × Int) =>
        let s := (s + (xs.getD (i).toNat 0))
        ForInStep.yield (none, s))) with
  | (some r, _) => r
  | (none, s) =>
    s
