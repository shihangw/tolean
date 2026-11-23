import tolean.Experimental.LoopCore.Cpp

namespace tolean.Experimental.LoopCore.Examples

open C
open tolean.Core.Loop

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
    | .count, [a, n] => s!"(tolean.Experimental.LoopCore.C.count {a} {n})"
    | _, _ => "unsupported_experimental_operation"

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

def repeatedWrite : Stmt := .assign "s" (.int 1) (.assign "s" (.int 2) .skip)
def branchWrite : Stmt :=
  .ite (.order .lt (.var "s") (.int 1))
    (.assign "s" (.int 1) .skip) (.assign "s" (.int 2) .skip)
def booleanState : Stmt := .assign "flag" (.bool true) .skip
def booleanReturn : Stmt := .ret (.bool true)

example : writes repeatedWrite = ["s"] := by decide
example : writes branchWrite = ["s"] := by decide
example : writes (.assign "b" (.int 0)
    (.assign "a" (.int 0) (.assign "b" (.int 1) .skip))) = ["b", "a"] := by decide

def modelSpan : Span := ⟨⟨1, 1⟩, ⟨1, 2⟩⟩
def head : C.Head := ⟨modelSpan, "i", 0, 4⟩
def range : Cpp.Head := .byConstRef modelSpan "x" "xs"
def valueRange : Cpp.Head := .byValue modelSpan "x" "xs"

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

example : result (C.runLoop head sumBody (input [1, 2, 3, 4])) = some 10 := by decide
example : result (evalIR semantics (input [1, 2, 3, 4]) sumIR) = some 10 := by decide
example : result (C.runLoop head findBody (input [1, 2, 3, 4])) = some 2 := by decide
example : result (evalIR semantics (input [1, 2, 3, 4]) findIR) = some 2 := by decide
example : result (C.runLoop head clampBody (input [-1, 2, 3, 4])) = some 5 := by decide
example : result (evalIR semantics (input [-1, 2, 3, 4]) clampIR) = some 5 := by decide
example : result (Cpp.runLoop range rangeSum (input [1, 2, 3, 4])) = some 10 := by decide
example : result (evalIR semantics (input [1, 2, 3, 4]) cppSumIR) = some 10 := by decide
example : result (Cpp.runLoop valueRange rangeFind (input [1, 2, 3, 4])) = some 3 := by decide
example : result (evalIR semantics (input [1, 2, 3, 4]) cppFindIR) = some 3 := by decide
example : result (evalIR semantics (input [1, 2, 3, 4]) twoIR) = some 13 := by decide
example : result (evalIR semantics (input []) cppSumIR) = some 0 := by decide
example : result (evalIR semantics (input [1, 2, 3, 4] 7) findIR) = some (-1) := by decide
example : result (evalIR semantics (input [1, 2, 3, 4] 7) cppFindIR) = some (-1) := by decide
example : result (evalIR semantics (input [-1, -2, -3, -4]) clampIR) = some 0 := by decide

def runTwo (env : Env) : Option (Outcome Env Val) := do
  match ← Cpp.runLoop range rangeSum env with
  | .normal inner => Cpp.runLoop valueRange second inner
  | other => return other

example : result (runTwo (input [1, 2, 3, 4])) = some 13 := by decide
example : head.safe sumBody = true := by decide
example : range.accepts rangeSum = true := by decide
example : range.accepts (.assign "xs" (.int 0) .skip) = false := by decide
example : head.safe (.assign "i" (.int 0) .skip) = false := by decide

example : (C.translateChecked head booleanState (.value (.int 0))).isOk = false := by decide
example : (C.translateChecked head booleanReturn (.value (.int 0))).isOk = false := by decide
example : (Cpp.translateChecked range booleanState (.value (.int 0))).isOk = false := by decide
example : (Cpp.translateChecked range booleanReturn (.value (.int 0))).isOk = false := by decide
example : (C.translateChecked head (.ret (.eq (.int 1) (.int 1)))
    (.value (.int 0))).isOk = false := by decide
example : (Cpp.translateChecked range (.assign "flag" (.eq (.int 1) (.int 1)) .skip)
    (.value (.int 0))).isOk = false := by decide

def golden (name : String) (body : Body) : String :=
  "import tolean.Experimental.LoopCore.Examples\n\n" ++
  s!"def {name} (xs : List Int) (key limit : Int) : Int :=\n  let s : Int := 0\n" ++
  String.intercalate "\n" ((body.lines {}).map ("  " ++ ·)) ++ "\n"

end tolean.Experimental.LoopCore.Examples
