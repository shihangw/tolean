import tolean.Prototype.LoopCore.Go

namespace tolean.Prototype.LoopCore.GoExamples

open tolean.Go

def var (n : String) : Syntax.Expr := .ident default n
def lit (n : String) : Syntax.Expr := .lit default .int n
def add : Syntax.Stmt := .assign default "+=" [var "s"] [var "x"]
def sum : Syntax.Stmt := .block default [add]
def find : Syntax.Stmt := .ifStmt default none (.binary default "==" (var "x") (var "key"))
  (.ret default [var "x"]) none
def clamp : Syntax.Stmt := .block default [
  .ifStmt default none (.binary default "<" (var "x") (lit "0")) (.cont default) none,
  add,
  .ifStmt default none (.binary default ">" (var "s") (var "limit")) (.brk default) none]

def loop (body : Syntax.Stmt) : Syntax.Stmt :=
  .range default (some ":=") (some (var "_")) (some (var "x")) (var "xs") body

def result (out : Option Go.Result) : Option Eval.Val := do
  match ← out with
  | .normal env => env.lookup "s"
  | .ret v => some v
  | _ => none

def run (xs : List Int) (body : Syntax.Stmt) : Option Eval.Val :=
  result (Go.run ⟨[], []⟩ (fun n => if n = "xs" then some (xs.map Eval.Val.int) else none)
    8 [("s", .int 0), ("key", .int 3), ("limit", .int 4)] (loop body))

#guard run [1,2,3,4] sum = some (.int 10)
#guard run [1,2,3,4] find = some (.int 3)
#guard run [-1,2,3,4] clamp = some (.int 5)
#guard run [] sum = some (.int 0)
#guard run [-1,-2,-3] clamp = some (.int 0)

end tolean.Prototype.LoopCore.GoExamples
