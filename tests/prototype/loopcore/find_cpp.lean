import tolean.Prototype.LoopCore.Examples

def find_cpp (xs : List Int) (key limit : Int) : Int :=
  let s : Int := 0
  match Id.run (forIn xs none
      (fun (x : Int) (_ : Option Int) =>
        if x = key then
          ForInStep.done (some x)
        else
          ForInStep.yield none)) with
  | some r => r
  | none =>
    (-1 : Int)
