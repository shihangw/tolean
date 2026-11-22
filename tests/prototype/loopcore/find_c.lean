import tolean.Prototype.LoopCore.Examples

def find_c (xs : List Int) (key limit : Int) : Int :=
  let s : Int := 0
  match Id.run (forIn (tolean.Prototype.LoopCore.C.count (0 : Int) (4 : Int)) none
      (fun (i : Int) (_ : Option Int) =>
        if (xs.getD (i).toNat 0) = key then
          ForInStep.done (some i)
        else
          ForInStep.yield none)) with
  | some r => r
  | none =>
    (-1 : Int)
