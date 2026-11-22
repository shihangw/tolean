import tolean.Prototype.LoopCore.Cpp

namespace tolean.Prototype.LoopCore.Examples

open C

instance : IR.PrintTy Empty where
  print _ t := nomatch t
  namesParam _ t := nomatch t
  binders _ := ""
  map _ := "Std.HashMap"
  set _ := "Std.HashSet"

instance : IR.PrintOp Op where
  print _ op args :=
    match op, args with
    | .at, [xs, i] => s!"({xs}.getD ({i}).toNat 0)"
    | .count, [a, n] => s!"(tolean.Prototype.LoopCore.C.count {a} {n})"
    | _, _ => "unsupported_prototype_operation"

def element : Expr := .ext .at [.var "xs", .var "i"]
def sumBody : Stmt := .addAssign "s" element .skip
def findBody : Stmt := .ite (.eq element (.var "key")) (.ret (.var "i")) .skip
def clampBody : Stmt :=
  .ite (.order .lt element (.int 0)) .cont
    (.addAssign "s" element (.ite (.order .lt (.var "limit") (.var "s")) .brk .skip))
def rangeSum : Stmt := .addAssign "s" (.var "x") .skip
def rangeFind : Stmt := .ite (.eq (.var "x") (.var "key")) (.ret (.var "x")) .skip
def second : Stmt := .ite (.eq (.var "x") (.var "key"))
  (.ret (.intOp .add (.var "s") (.var "x"))) .skip

def head : C.Head := ⟨"i", 0, 4⟩
def range : Cpp.Head := .byConstRef "x" "xs"
def valueRange : Cpp.Head := .byValue "x" "xs"

def sumIR : Body := C.translateLoop head sumBody (.value (.var "s"))
def findIR : Body := C.translateLoop head findBody (.value (.int (-1)))
def clampIR : Body := C.translateLoop head clampBody (.value (.var "s"))
def cppSumIR : Body := Cpp.translateLoop range rangeSum (.value (.var "s"))
def cppFindIR : Body := Cpp.translateLoop valueRange rangeFind (.value (.int (-1)))
def twoIR : Body := Cpp.translateLoop range rangeSum
  (Cpp.translateLoop valueRange second (.value (.var "s")))

def input (xs : List Int) (key : Int := 3) (limit : Int := 4) : Env :=
  fun n => if n = "xs" then .array xs else if n = "key" then .int key
    else if n = "limit" then .int limit else .int 0

def result (out : Option (Outcome Env Val)) : Option Int := do
  match ← out with
  | .ret (.int n) => some n
  | .normal env => match env "s" with | .int n => some n | _ => none
  | _ => none

example : result (C.runLoop head sumBody (input [1,2,3,4])) = some 10 := by decide
example : result (evalIR semantics (input [1,2,3,4]) sumIR) = some 10 := by decide
example : result (C.runLoop head findBody (input [1,2,3,4])) = some 2 := by decide
example : result (evalIR semantics (input [1,2,3,4]) findIR) = some 2 := by decide
example : result (C.runLoop head clampBody (input [-1,2,3,4])) = some 5 := by decide
example : result (evalIR semantics (input [-1,2,3,4]) clampIR) = some 5 := by decide
example : result (Cpp.runLoop range rangeSum (input [1,2,3,4])) = some 10 := by decide
example : result (evalIR semantics (input [1,2,3,4]) cppSumIR) = some 10 := by decide
example : result (Cpp.runLoop valueRange rangeFind (input [1,2,3,4])) = some 3 := by decide
example : result (evalIR semantics (input [1,2,3,4]) cppFindIR) = some 3 := by decide
example : result (evalIR semantics (input [1,2,3,4]) twoIR) = some 13 := by decide
example : result (evalIR semantics (input []) cppSumIR) = some 0 := by decide
example : result (evalIR semantics (input [1,2,3,4] 7) findIR) = some (-1) := by decide
example : result (evalIR semantics (input [1,2,3,4] 7) cppFindIR) = some (-1) := by decide
example : result (evalIR semantics (input [-1,-2,-3,-4]) clampIR) = some 0 := by decide

def golden (name : String) (body : Body) : String :=
  "import tolean.Prototype.LoopCore.Examples\n\n" ++
  s!"def {name} (xs : List Int) (key limit : Int) : Int :=\n  let s : Int := 0\n" ++
  String.intercalate "\n" ((body.lines {}).map ("  " ++ ·)) ++ "\n"

end tolean.Prototype.LoopCore.Examples
