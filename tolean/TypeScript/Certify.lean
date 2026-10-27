import tolean.TypeScript.Syntax.Parser
import tolean.TypeScript.Certify.Term
import tolean.TypeScript.Spec.Eval
import tolean.TypeScript.Translate

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

A loop gets a lemma of its own before the theorem of its function. The lemma
states that the interpreter runs the loop as the translation's `List.foldl`,
for every environment whose variables have values of the right types. It
follows from `execLoop_foldl` in `Spec/Lemmas/Eval.lean`, and the theorem of
the function uses it as a rewrite rule. To be usable that way, the lemma reads
the loop's starting state, and the other variables that the body reads, back
out of the environment with decoders.

A `number` is a value of the abstract model `JSNumber N`, in the
interpreter as in the translation, so every theorem holds for every `N`.
-/
namespace tolean.TypeScript.Certify

open tolean tolean.TypeScript.Syntax

/-- How a value of a TypeScript type becomes a `Val`, as a Lean function. -/
partial def encoder : TypeExpr → Option String
  | .keyword _ "bigint" => some "Val.int"
  | .keyword _ "number" => some "Val.num"
  | .keyword _ "boolean" => some "Val.bool"
  | .keyword _ "string" => some "Val.str"
  | .paren _ t => encoder t
  | .union _ [a, b] => do
    let inner ← match a, b with
      | .null _, t | t, .null _ => encoder t
      | _, _ => none
    return s!"(encNull {inner})"
  | .array _ t => do return s!"(encList {← encoder t})"
  | .ref _ "Array" [t] | .ref _ "ReadonlyArray" [t] => do return s!"(encList {← encoder t})"
  | .ref _ name [] => some s!"encode{name}"
  | _ => none

/-- How a value of a Lean type of the output becomes a `Val`, as `encoder`
writes it. -/
def encoderOf : Output.Ty → Option String
  | .int => some "Val.int"
  | .bool => some "Val.bool"
  | .string => some "Val.str"
  | .option t => do return s!"(encNull {← encoderOf t})"
  | .list t => do return s!"(encList {← encoderOf t})"
  | .struct name => some s!"encode{name}"
  | .number => some "Val.num"
  | .null => none

/-- How a variable's value becomes a Lean value of type `t` again. -/
def decoderOf : Output.Ty → Option String
  | .int => some "decInt"
  | .bool => some "decBool"
  | .string => some "decStr"
  | .option t => do return s!"(decNull {← decoderOf t})"
  | .list t => do return s!"(decList {← decoderOf t})"
  | .struct name => some s!"decode{name}"
  | .number => some "decNum"
  | .null => none

/-- The statements of a function body, with nested ones. -/
partial def stmtsOf : Stmt → List Stmt
  | .block _ body => .block default body :: body.flatMap stmtsOf
  | .ifStmt s t a b => .ifStmt s t a b :: stmtsOf a ++ ((b.map stmtsOf).getD [])
  | .forOfStmt s k n i b => .forOfStmt s k n i b :: stmtsOf b
  | .whileStmt s t b => .whileStmt s t b :: stmtsOf b
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

/-- The text of each number literal in `e`. -/
partial def exprNumbers : Expr → List String
  | .number _ t => [t]
  | .call _ c args => exprNumbers c ++ args.flatMap exprNumbers
  | .paren _ e | .member _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e => exprNumbers e
  | .index _ a b | .binary _ _ a b | .assign _ _ a b => exprNumbers a ++ exprNumbers b
  | .cond _ a b c => exprNumbers a ++ exprNumbers b ++ exprNumbers c
  | .array _ es => es.flatMap exprNumbers
  | .object _ ps => ps.flatMap fun | .keyValue _ _ v => exprNumbers v | _ => []
  | _ => []

def stmtNumbers : Stmt → List String
  | .varDecl _ d => (d.init.map exprNumbers).getD []
  | .exprStmt _ e | .ifStmt _ e _ _ | .whileStmt _ e _ | .forOfStmt _ _ _ e _ => exprNumbers e
  | .returnStmt _ e => (e.map exprNumbers).getD []
  | _ => []

def stmtCalls : Stmt → List String
  | .varDecl _ d => (d.init.map exprCalls).getD []
  | .exprStmt _ e | .ifStmt _ e _ _ | .whileStmt _ e _ | .forOfStmt _ _ _ e _ => exprCalls e
  | .returnStmt _ e => (e.map exprCalls).getD []
  | _ => []

def functionsOf (m : Module) : List (String × List Param × Option TypeExpr × Stmt) :=
  m.decls.filterMap fun
    | .function _ _ n ps r b => some (n, ps, r, b)
    | _ => none

/-- The functions that get a certificate: all of them. -/
def certifiable (m : Module) : List String := (functionsOf m).map (·.1)

/-- How deep the calls in `s` nest: the fuel that the interpreter needs to run
them. The subset has no recursion, so the depth is finite. -/
partial def callDepth (m : Module) (s : Stmt) : Nat :=
  let rec go (fuel : Nat) (s : Stmt) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
      ((stmtsOf s).flatMap stmtCalls).foldl (init := 0) fun acc f =>
        match (functionsOf m).find? (·.1 == f) with
        | some (_, _, _, body) => max acc (go fuel body + 1)
        | none => acc
  go ((functionsOf m).length + 1) s

/-- The body of the `for…of` statement at `span`. -/
def loopBody (s : Stmt) (span : Span) : Option Stmt :=
  (stmtsOf s).findSome? fun
    | .forOfStmt sp _ _ _ body => if sp == span then some body else none
    | _ => none

partial def isNullable : TypeExpr → Bool
  | .union _ [.null _, _] | .union _ [_, .null _] => true
  | .paren _ t => isNullable t
  | _ => false

/-- Split each nullable parameter first, so that each case sees a known
value. -/
def casesOn (params : List Param) : String :=
  String.join (params.filterMap fun p =>
    if (p.type.map isNullable).getD false then some s!"cases {p.name} <;> " else none)

/-- The loops of a body, inner ones first, in the order of the source. -/
partial def loopsOf : Output.Body → List (List String × String × Output.Body × Output.LoopInfo)
  | .value _ | .state _ => []
  | .let _ _ rest | .letArray _ _ _ rest => loopsOf rest
  | .ite _ a b | .matchNull _ a b => loopsOf a ++ loopsOf b
  | .letState _ branch rest => loopsOf branch ++ loopsOf rest
  | .fold names element body _ rest info => loopsOf body ++ [(names, element, body, info)] ++ loopsOf rest

/-- `s`, the state of a loop with the locals `names`, as the path to one of
them: `s`, `s.1`, `s.2.1`, and so on. -/
def project (s : String) (count index : Nat) : String :=
  if count == 1 then s
  else
    let seconds := String.join (List.replicate index ".2")
    if index + 1 == count then s!"{s}{seconds}" else s!"{s}{seconds}.1"

/-- The certificate file for `source`, translated as the Lean module `leanModule`
with namespace `transNs`. -/
def certify (file source leanModule transNs certNs : String) (target : Edition := .default) :
    Except String String := do
  let (m, names, decls) ← Translate.translateTree file source target
  let names := { names with namespacePrefix := transNs ++ "." }
  let fns := certifiable m
  if fns.isEmpty then throw s!"{file}: there is no function to certify"
  let nv := names.numberVar
  -- Every theorem is about every number model.
  let generic := s!"\{{nv} : Type} [tolean.TypeScript.JSNumber {nv}]"
  -- A generic translated definition takes the model by name, as the
  -- translation's own calls do.
  let callN := if names.usesNumber then s!" ({nv} := {nv})" else ""
  let structTy (name : String) : String := (Output.Ty.struct name).print names
  let mut encs : Array String := #[]
  let mut lemmaNames : Array String :=
    #["encList", "encNull", "decInt", "decBool", "decStr", "decNum"]
  for d in decls do
    if let .struct name fields := d then
      let parts ← fields.mapM fun (f, t) => do
        let some e := encoderOf t | throw s!"{file}: cannot encode the field {name}.{f}"
        return s!"({str f}, {e} x.{f})"
      let decs ← fields.mapM fun (f, t) => do
        let some dec := decoderOf t | throw s!"{file}: cannot decode the field {name}.{f}"
        return (f, dec)
      let some_ := ", ".intercalate (decs.map fun (f, dec) => s!"{f} := {dec} (fs.lookup {str f})")
      let none_ := ", ".intercalate (decs.map fun (f, dec) => s!"{f} := {dec} (none : Option (Val {nv}))")
      encs := encs.push s!"def encode{name} {generic} (x : {structTy name}) : Val {nv} := Val.obj {list parts}"
      encs := encs.push <|
        s!"def decode{name} {generic} : Option (Val {nv}) → {structTy name}\n" ++
        s!"  | some (.obj fs) => \{ {some_} }\n" ++
        s!"  | _ => \{ {none_} }"
      encs := encs.push <|
        s!"@[simp] theorem decode{name}_encode{name} {generic} (x : {structTy name}) : decode{name} (some (encode{name} ({nv} := {nv}) x)) = x := by\n" ++
        s!"  cases x; simp [decode{name}, encode{name}, List.lookup, encList, encNull]"
      lemmaNames := lemmaNames ++ #[s!"encode{name}", s!"decode{name}"]
  let defs := (functionsOf m).map (s!"{transNs}." ++ ·.1)
  -- `simp` cannot run `numberLiteral`, so each literal gets a lemma that
  -- `decide` proves.
  let texts := ((functionsOf m).flatMap fun (_, _, _, b) => (stmtsOf b).flatMap stmtNumbers).eraseDups
  let mut literals : Array String := #[]
  for (text, i) in texts.zipIdx do
    let value := match Eval.numberLiteral text with
      | some v => s!"some ({v})"
      | none => "none"
    encs := encs.push s!"theorem numberLiteral{i} : numberLiteral {str text} = {value} := by decide"
    literals := literals.push s!"numberLiteral{i}"
  lemmaNames := lemmaNames ++ literals
  let envLemmas := ["Env.set_cons", "Env.lookup_cons", "Env.lookup_set_same", "Env.lookup_set_ne",
    "Env.set_set", "Env.length_set"]
  let mut loopLemmas : Array String := #[]
  let mut thms : Array String := #[]
  for d in m.decls do
    let .function _ _ name params ret syntaxBody := d | continue
    unless fns.contains name do continue
    let some (.function _ _ _ outBody) := decls.find? fun
        | .function n .. => n == name
        | _ => false
      | throw s!"{file}: no translation of {name}"
    let mut index := 0
    for (stateNames, element, body, info) in loopsOf outBody do
      index := index + 1
      let lemmaName := s!"{name}_loop{index}"
      let some bodyStmt := loopBody syntaxBody info.span
        | throw s!"{file}: no loop at {info.span.start.line}:{info.span.start.col} in {name}"
      let some encX := encoderOf info.elem | throw s!"{file}: cannot encode the elements of a loop in {name}"
      let state := stateNames.zip info.stateTypes
      let vars := state ++ info.scope
      let coded ← vars.mapM fun (n, t) => do
        let (some e, some dec) := (encoderOf t, decoderOf t)
          | throw s!"{file}: cannot encode the variable {n} in {name}"
        return (n, e, dec)
      let decode (ρ n : String) : String :=
        match coded.find? (·.1 == n) with
        | some (_, _, dec) => s!"({dec} ({ρ}.lookup {str n}))"
        | none => "default"
      let count := stateNames.length
      let upd (s ρ : String) : String :=
        (stateNames.zipIdx.foldl (init := ρ) fun acc (n, i) =>
          match coded.find? (·.1 == n) with
          | some (_, e, _) => s!"({acc}.set {str n} ({e} {project s count i}))"
          | none => acc)
      let decState (ρ : String) : String :=
        if count == 1 then decode ρ stateNames.head! else
          "(" ++ ", ".intercalate (stateNames.map (decode ρ)) ++ ")"
      -- The globals that the interpreter reads when no variable hides them.
      let globals := ["Number", "NaN", "Infinity"].filter fun g => !vars.any (·.1 == g)
      let inv (ρ : String) : String :=
        " ∧ ".intercalate ((coded.map fun (n, e, dec) =>
          s!"{ρ}.lookup {str n} = some ({e} ({dec} ({ρ}.lookup {str n})))") ++
          globals.map fun g => s!"{ρ}.lookup {str g} = none")
      let scopeNames := info.scope.map (·.1)
      let stepLines := Output.indentBy "        " (body.lines names)
      let captured := if scopeNames.isEmpty then "" else s!"fun {" ".intercalate scopeNames} => "
      let stepFn (ρ : String) : String :=
        s!"((({captured}fun {Output.tuple stateNames} {element} =>\n" ++ "\n".intercalate stepLines ++ ")" ++
          String.join (scopeNames.map fun n => s!" {decode ρ n}") ++ "))"
      let depth := callDepth m bodyStmt
      let fuel := if depth == 0 then "fuel" else s!"(fuel + {depth})"
      let hm := if depth == 0 then "" else " (hm : m = program)"
      let hmName := if depth == 0 then [] else ["program"]
      let substHm := if depth == 0 then "" else "    subst hm\n"
      let elemTy := info.elem.print names
      let hypNames := (List.range (coded.length + globals.length)).map (s!"h{·}")
      let hyps := if hypNames.length == 1 then "h0" else "⟨" ++ ", ".intercalate hypNames ++ "⟩"
      let generalize (ρ : String) (which : List (String × String × String)) : String :=
        String.join (which.zipIdx.map fun ((n, _, dec), i) =>
          s!"    generalize {dec} ({ρ}.lookup {str n}) = v{i} at h{i} ⊢\n")
      let stateCoded := coded.take count
      let destruct := if count ≤ 1 then "" else
        s!"    obtain ⟨{", ".intercalate ((List.range count).map (s!"s{·}"))}⟩ := s\n"
      let simpSet := ", ".intercalate (hmName ++ envLemmas ++ lemmaNames.toList ++ loopLemmas.toList ++ defs)
      loopLemmas := loopLemmas.push lemmaName
      thms := thms.push <|
        s!"theorem {lemmaName} {generic} (m : tolean.TypeScript.Syntax.Module){hm} (fuel : Nat) (items : List {elemTy}) (ρ : Env {nv})\n" ++
        s!"    (hI : {inv "ρ"}) :\n" ++
        s!"    execLoop m {fuel} ρ {str element} {stmt bodyStmt} (List.map {encX} items) =\n" ++
        s!"      some (.normal {upd s!"(List.foldl {stepFn "ρ"} {decState "ρ"} items)" "ρ"}) := by\n" ++
        s!"  refine execLoop_foldl m {fuel} {str element} _ {encX} (fun s ρ => {upd "s" "ρ"})\n" ++
        s!"    (fun ρ => {decState "ρ"}) (fun ρ => {stepFn "ρ"}) (fun ρ => {inv "ρ"}) ?_ ?_ ?_ items ρ hI\n" ++
        s!"  · intro ρ s x hI\n" ++ substHm ++
        s!"    obtain {hyps} := hI\n    try simp only []\n" ++
        generalize "ρ" coded ++ destruct ++
        s!"    certify_tac [{simpSet}, {", ".intercalate hypNames}]\n" ++
        s!"  · intro s ρ; simp [Env.length_set]\n" ++
        s!"  · intro ρ hI\n" ++
        s!"    obtain {hyps} := hI\n    try simp only []\n" ++
        generalize "ρ" stateCoded ++
        s!"    simp [{", ".intercalate ((List.range count).map fun i => s!"Env.set_of_lookup _ _ _ h{i}")}]"
    let some retEnc := ret.bind encoder | throw s!"{file}: cannot encode the result of {name}"
    let args ← params.mapM fun p => do
      let some e := p.type.bind encoder | throw s!"{file}: cannot encode the parameter {p.name}"
      return s!"({e} {p.name})"
    let binders := " ".intercalate (params.map fun p => s!"({p.name} : _)")
    let call := " ".intercalate (s!"{transNs}.{name}{callN}" :: params.map (·.name))
    let simpSet := ", ".intercalate (["program"] ++ envLemmas ++ lemmaNames.toList ++ loopLemmas.toList ++ defs)
    thms := thms.push <|
      s!"theorem {name}_cert {generic} {binders} :\n" ++
      s!"    run (N := {nv}) program {str name} {list args} = some ({retEnc} ({call})) := by\n" ++
      s!"  {casesOn params}certify_tac [{simpSet}]"
  return "\n".intercalate ([
    s!"-- Certificate written by tolean for {file}. Do not edit.",
    "import tolean.TypeScript.Spec.Lemmas.Eval",
    s!"import {leanModule}",
    "",
    s!"namespace {certNs}",
    "",
    "open tolean.TypeScript tolean.TypeScript.Eval",
    "",
    "-- The proofs pass the same lemmas everywhere, so some go unused.",
    "set_option linter.unusedSimpArgs false",
    "set_option linter.unusedVariables false",
    "",
    "/-- The program, as the parser read it. -/",
    s!"def program : tolean.TypeScript.Syntax.Module :=\n  {module m}",
    ""] ++ encs.toList.map (· ++ "\n") ++ thms.toList.map (· ++ "\n") ++ [s!"end {certNs}", ""])

/-- The functions of `source` that get a certificate, and whether that is all
of them. -/
def certifiedFunctions (source : String) (target : Edition := .default) :
    Except String (List String × Bool) := do
  let m ← (parse source target).mapError (·.message)
  let all := m.decls.filterMap fun | .function _ _ n .. => some n | _ => none
  let fns := certifiable m
  return (fns, fns.length == all.length)

end tolean.TypeScript.Certify
