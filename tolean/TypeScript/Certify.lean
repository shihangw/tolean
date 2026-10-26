import tolean.TypeScript.Syntax.Parser
import tolean.TypeScript.Certify.Term
import tolean.TypeScript.Spec.Eval

/-!
`tolean certify`: a per-file certificate for a translation.

For one TypeScript file, the certificate holds the parsed program as a Lean
term, an encoding of each translated Lean value as a JavaScript value, and one
theorem per function:

```
theorem raise_cert (g step) :
    run program "raise" [encGauge g, .int step] = some (encGauge (raise g step))
```

`run` is the interpreter in `Spec/Eval.lean`. When the theorems compile, the
translation of that file is proved: for every input, the translated function
returns what the program returns. This module does not need to be trusted. If
it writes a wrong encoding or a wrong theorem, Lean refuses the file.

A function gets a certificate when it and every function it calls have no
loops and no `number` values. Loops come in a later phase.
-/
namespace tolean.TypeScript.Certify

open tolean tolean.TypeScript.Syntax

/-- How a value of a TypeScript type becomes a `Val`, as a Lean function. -/
partial def encoder : TypeExpr → Option String
  | .keyword _ "bigint" => some "Val.int"
  | .keyword _ "boolean" => some "Val.bool"
  | .keyword _ "string" => some "Val.str"
  | .paren _ t => encoder t
  | .union _ [a, b] => do
    let inner ← match a, b with
      | .null _, t | t, .null _ => encoder t
      | _, _ => none
    return s!"(fun o => match o with | some v => {inner} v | none => Val.null)"
  | .array _ t => do return s!"(fun xs => Val.list (xs.map {← encoder t}))"
  | .ref _ "Array" [t] | .ref _ "ReadonlyArray" [t] => do
    return s!"(fun xs => Val.list (xs.map {← encoder t}))"
  | .ref _ name [] => some s!"enc{name}"
  | _ => none

/-- The source uses the abstract number model: `NaN`, `Infinity` or `Number`. -/
def usesNumberNames (source : String) (target : Edition) : Bool :=
  match lex source target with
  | .ok tokens => tokens.any fun (t : Token) => match t.kind with
    | .ident n => n == "NaN" || n == "Infinity" || n == "Number"
    | _ => false
  | .error _ => true

/-- The statements of a function body, with nested ones. -/
partial def stmtsOf : Stmt → List Stmt
  | .block _ body => .block default body :: body.flatMap stmtsOf
  | .ifStmt s t a b => .ifStmt s t a b :: stmtsOf a ++ ((b.map stmtsOf).getD [])
  | s => [s]

partial def exprCalls : Expr → List String
  | .call _ (.ident _ f) args => f :: args.flatMap exprCalls
  | .call _ c args => exprCalls c ++ args.flatMap exprCalls
  | .paren _ e | .member _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e => exprCalls e
  | .index _ a b | .binary _ _ a b | .assign _ _ a b => exprCalls a ++ exprCalls b
  | .cond _ a b c => exprCalls a ++ exprCalls b ++ exprCalls c
  | .array _ es => es.flatMap exprCalls
  | .object _ ps => ps.flatMap fun | .keyValue _ _ v => exprCalls v | _ => []
  | _ => []

def stmtCalls : Stmt → List String
  | .varDecl _ d => (d.init.map exprCalls).getD []
  | .exprStmt _ e | .ifStmt _ e _ _ | .whileStmt _ e _ | .forOfStmt _ _ _ e _ => exprCalls e
  | .returnStmt _ e => (e.map exprCalls).getD []
  | _ => []

def hasLoop (body : Stmt) : Bool :=
  (stmtsOf body).any fun | .forOfStmt .. | .whileStmt .. => true | _ => false

partial def typeHasNumber : TypeExpr → Bool
  | .keyword _ "number" => true
  | .paren _ t | .array _ t => typeHasNumber t
  | .union _ ts | .ref _ _ ts => ts.any typeHasNumber
  | _ => false

/-- The functions that get a certificate: no loops and no `number`, in
themselves and in every function they call. -/
def certifiable (m : Module) : List String :=
  let fns := m.decls.filterMap fun
    | .function _ _ n ps r b => some (n, ps, r, b)
    | _ => none
  let structsUseNumber := m.decls.any fun
    | .interface _ _ _ fs => fs.any (typeHasNumber ·.type)
    | _ => false
  let ok1 (n : String) : Bool := match fns.find? (·.1 == n) with
    | some (_, ps, r, b) =>
      !hasLoop b && !structsUseNumber && !ps.any (fun p => (p.type.map typeHasNumber).getD true) &&
        !((r.map typeHasNumber).getD true)
    | none => false
  -- A function is certifiable when it and all it reaches are.
  let rec reach (fuel : Nat) (seen : List String) (n : String) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if seen.contains n then true
      else ok1 n && match fns.find? (·.1 == n) with
        | some (_, _, _, b) => ((stmtsOf b).flatMap stmtCalls).all (reach fuel (n :: seen))
        | none => false
  fns.filterMap fun (n, _, _, _) => if reach (fns.length + 1) [] n then some n else none

partial def isNullable : TypeExpr → Bool
  | .union _ [.null _, _] | .union _ [_, .null _] => true
  | .paren _ t => isNullable t
  | _ => false

/-- Split each nullable parameter first, so that each case sees a known
value. -/
def casesOn (params : List Param) : String :=
  String.join (params.filterMap fun p =>
    if (p.type.map isNullable).getD false then some s!"cases {p.name} <;> " else none)

/-- The functions of `source` that get a certificate, and whether that is all
of them. -/
def certifiedFunctions (source : String) (target : Edition := .default) :
    Except String (List String × Bool) := do
  let m ← (parse source target).mapError (·.message)
  let all := m.decls.filterMap fun | .function _ _ n .. => some n | _ => none
  let fns := if usesNumberNames source target then [] else certifiable m
  return (fns, fns.length == all.length)

/-- The certificate file for `source`, translated as the Lean module `leanModule`
with namespace `transNs`. -/
def certify (file source leanModule transNs certNs : String) (target : Edition := .default) :
    Except String String := do
  let m ← (parse source target).mapError (·.render file)
  let fns := if usesNumberNames source target then [] else certifiable m
  if fns.isEmpty then throw s!"{file}: no function can get a certificate yet (loops and number come later)"
  let mut encs : Array String := #[]
  let mut encNames : Array String := #[]
  for d in m.decls do
    if let .interface _ _ name fields := d then
      let parts ← fields.mapM fun f => do
        let some e := encoder f.type | throw s!"{file}: cannot encode the field {name}.{f.name}"
        return s!"({str f.name}, {e} x.{f.name})"
      encs := encs.push s!"def enc{name} (x : {transNs}.{name}) : Val := Val.obj {list parts}"
      encNames := encNames.push s!"enc{name}"
  let mut thms : Array String := #[]
  let defs := m.decls.filterMap fun
    | .function _ _ n _ _ _ => some n
    | _ => none
  for d in m.decls do
    let .function _ _ name params ret _ := d | continue
    unless fns.contains name do continue
    let some retEnc := ret.bind encoder | throw s!"{file}: cannot encode the result of {name}"
    let args ← params.mapM fun p => do
      let some e := p.type.bind encoder | throw s!"{file}: cannot encode the parameter {p.name}"
      return s!"({e} {p.name})"
    let binders := " ".intercalate (params.map fun p => s!"({p.name} : _)")
    let call := " ".intercalate (s!"{transNs}.{name}" :: params.map (·.name))
    thms := thms.push <|
      s!"theorem {name}_cert {binders} :\n" ++
      s!"    run program {str name} {list args} = some ({retEnc} ({call})) := by\n" ++
      s!"  {casesOn params}certify_tac [program, {", ".intercalate (encNames.toList ++ defs.map (s!"{transNs}." ++ ·))}]"
  return "\n".intercalate ([
    s!"-- Certificate written by tolean for {file}. Do not edit.",
    "import tolean.TypeScript.Spec.Eval",
    s!"import {leanModule}",
    "",
    s!"namespace {certNs}",
    "",
    "open tolean.TypeScript.Eval",
    "",
    "/-- The program, as the parser read it. -/",
    s!"def program : tolean.TypeScript.Syntax.Module :=\n  {module m}",
    ""] ++ encs.toList.map (· ++ "\n") ++ thms.toList.map (· ++ "\n") ++ [s!"end {certNs}", ""])

end tolean.TypeScript.Certify
