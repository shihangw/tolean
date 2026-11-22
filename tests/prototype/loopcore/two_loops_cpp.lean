import tolean.Prototype.LoopCore.Examples

def two_loops_cpp (xs : List Int) (key limit : Int) : Int :=
  let s : Int := 0
  match Id.run (forIn xs (none, s)
      (fun (x : Int) ((_, s) : Option Int × Int) =>
        let s := (s + x)
        ForInStep.yield (none, s))) with
  | (some r, _) => r
  | (none, s) =>
    match Id.run (forIn xs none
        (fun (x : Int) (_ : Option Int) =>
          if x = key then
            ForInStep.done (some (s + x))
          else
            ForInStep.yield none)) with
    | some r => r
    | none =>
      s
