import Lean.Util.CollectAxioms
import Lean.Util.Path
import tolean.Chain.Emit

/-!
`tolean chain check`, `graph` and `trust`: read a project manifest and the
file manifests it lists.

`check` fails when a file changed since it was translated, a node's status has
no evidence, or a claim's proof is not a theorem of exactly the claim with the
recorded axioms. It loads the proofs from the `.olean` files, so run it under
`lake env` after `lake build`.
-/
namespace tolean.Chain

open Lean

structure Loaded where
  dir : System.FilePath
  project : ProjectManifest
  files : List (String × FileManifest)

def load (path : System.FilePath) : IO Loaded := do
  let dir := path.parent.getD "."
  let project : ProjectManifest ← readJson path
  let files ← project.files.mapM fun (f : String) => do return (f, ← readJson (A := FileManifest) (dir / f))
  return { dir, project, files }

/-- Node ids in a file manifest are local; the project sees them as `module:id`,
and the output as the module itself. -/
def qualify (m : FileManifest) (id : String) : String :=
  if id == "output" then m.module else s!"{m.module}:{id}"

def allNodes (l : Loaded) : List (String × Node) :=
  l.files.flatMap (fun (_, m) => m.nodes.map fun n => (qualify m n.id, n)) ++
  l.project.nodes.map fun n => (n.id, n)

def allEdges (l : Loaded) : List (String × String) :=
  l.files.flatMap (fun (_, m) => m.edges.map fun (a, b) => (qualify m a, qualify m b)) ++
  l.project.edges ++
  l.project.claims.flatMap fun c => c.depends.map (·, c.id)

/-! ### check -/

private def freshness (l : Loaded) : IO (List String) := do
  let mut errs := []
  for (f, m) in l.files do
    for r in m.sources ++ [m.output] do
      let p := l.dir / r.path
      if !(← p.pathExists) then
        errs := errs ++ [s!"{f}: {r.path} is missing"]
      else if sha256Hex (← IO.FS.readBinFile p) != r.sha256 then
        errs := errs ++ [s!"{f}: {r.path} changed since it was translated; translate it again"]
  return errs

private def evidence (l : Loaded) (passed : List String) : List String :=
  l.files.flatMap (fun (f, m) => m.nodes.filterMap fun n => nodeErr s!"{f}: {n.id}" m.tolean n) ++
  l.project.nodes.filterMap fun n => nodeErr s!"project: {n.id}" version n
where
  nodeErr (at_ tool : String) (n : Node) : Option String :=
    match n.status, n.evidence with
    | .tested, none => some s!"{at_} is tested, but names no check"
    | .tested, some e =>
      match e.check, e.«by» with
      | none, _ => some s!"{at_} is tested, but names no check"
      | some c, some "tolean" =>
        if tool == version then none
        else some s!"{at_}: check {c} ran on tolean {version}, not on {tool}; translate again"
      | some c, some "project" =>
        if passed.contains c then none else some s!"{at_}: check {c} did not pass (see --passed)"
      | some c, _ => some s!"{at_}: check {c} must say by tolean or by project"
    | .proved, _ =>
      if n.«theorem».isNone || n.module.isNone then some s!"{at_} is proved, but names no theorem"
      else none
    | _, _ => none

private instance : MonadEnv (ReaderT Environment Id) where
  getEnv := read
  modifyEnv _ := pure ()

/-- `name` is a theorem whose axioms are among `allowed`; with `spec`, its type
is the constant `spec`. -/
private def theoremErr (env : Environment) (at_ name : String) (spec : Option String)
    (allowed : List String) : Option String := Id.run do
  let n := name.toName
  let some ci := env.find? n | return some s!"{at_}: {name} is not in the environment"
  unless ci matches .thmInfo _ do return some s!"{at_}: {name} is not a theorem"
  if let some s := spec then
    unless ci.type == mkConst s.toName do
      return some s!"{at_}: the type of {name} is not exactly {s}"
    if env.find? s.toName |>.isNone then return some s!"{at_}: {s} is not in the environment"
  let axs := (collectAxioms n : ReaderT Environment Id _).run env
  let extra := axs.toList.filter fun a => !allowed.contains a.toString
  if extra.isEmpty then none
  else some s!"{at_}: {name} also depends on {", ".intercalate (extra.map toString)}"

private def proofs (l : Loaded) : IO (List String) := do
  let mods := (l.project.claims.map (·.module) ++
    (allNodes l).filterMap fun (_, n) => if n.status == .proved then n.module else none).eraseDups
  if mods.isEmpty then return []
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {}
  let claimErrs := l.project.claims.filterMap fun c =>
    theoremErr env s!"claim {c.id}" c.proof (some c.spec) c.axioms
  let nodeErrs := (allNodes l).filterMap fun (id, n) =>
    match n.status, n.«theorem» with
    | .proved, some t => theoremErr env id t none n.axioms
    | _, _ => none
  return claimErrs ++ nodeErrs

private def references (l : Loaded) : List String :=
  let known := (allNodes l).map (·.1) ++ l.files.map (·.2.module) ++ l.project.claims.map (·.id)
  l.project.claims.flatMap (fun c => c.depends.filterMap fun d =>
      if known.contains d then none else some s!"claim {c.id}: depends on unknown {d}") ++
  l.project.edges.flatMap fun (a, b) => [a, b].filterMap fun x =>
      if known.contains x then none else some s!"project edge: unknown {x}"

def check (path : System.FilePath) (passed : List String) : IO UInt32 := do
  let l ← load path
  let errs := (← freshness l) ++ evidence l passed ++ references l ++ (← proofs l)
  for e in errs do IO.eprintln e
  if errs.isEmpty then
    IO.println s!"{l.files.length} files, {(allNodes l).length} nodes, {l.project.claims.length} claims: the chain holds"
    return 0
  return 1

/-! ### graph -/

def Status.color : Status → String
  | .proved => "#e6f4ea\" color=\"#1e8e3e"
  | .tested => "#fef7e0\" color=\"#b06000"
  | .trusted => "#fce8e6\" color=\"#c5221f"
  | .readByPeople => "#e8f0fe\" color=\"#1a73e8"
  | .generated => "#f1f3f4\" color=\"#5f6368"
  | .planned => "#ffffff\" style=\"dashed,filled\" color=\"#5f6368"

private def esc (s : String) : String := s.replace "\"" "\\\""

/-- The chain in Graphviz DOT, colored by status. -/
def graph (path : System.FilePath) : IO UInt32 := do
  let l ← load path
  let mut out := "digraph chain {\n  rankdir=LR;\n  node [shape=box style=\"rounded,filled\" fontname=\"Helvetica\"];\n"
  for (_, m) in l.files do
    out := out ++ s!"  \"{esc m.module}\" [label=\"{esc m.module}\\n{m.language}, generated\" fillcolor=\"{Status.generated.color}\"];\n"
    let srcs := ", ".intercalate (m.sources.map (·.path))
    out := out ++ s!"  \"{esc (qualify m "source")}\" [label=\"{esc srcs}\\nsource\" shape=note fillcolor=\"#ffffff\" color=\"#9aa0a6\"];\n"
  for (id, n) in allNodes l do
    out := out ++ s!"  \"{esc id}\" [label=\"{esc n.label}\\n{n.status.name}\" fillcolor=\"{n.status.color}\"];\n"
  for c in l.project.claims do
    out := out ++ s!"  \"{esc c.id}\" [label=\"{esc c.id}\\n{esc c.proof}\" fillcolor=\"{Status.proved.color}\"];\n"
  for (a, b) in (allEdges l).eraseDups do
    out := out ++ s!"  \"{esc a}\" -> \"{esc b}\";\n"
  IO.print (out ++ "}\n")
  return 0

/-! ### trust -/

/-- What `claim` relies on that no proof covers: every node it reaches backwards
that is not proved, generated or a file. -/
def trust (path : System.FilePath) (claim : String) : IO UInt32 := do
  let l ← load path
  unless l.project.claims.any (·.id == claim) do
    IO.eprintln s!"no claim {claim}"
    return 1
  let edges := allEdges l
  let mut seen : List String := []
  let mut todo := [claim]
  while h : todo ≠ [] do
    let x := todo.head h
    todo := todo.tail
    unless seen.contains x do
      seen := x :: seen
      todo := todo ++ (edges.filter (·.2 == x)).map (·.1)
  for (id, n) in allNodes l do
    if seen.contains id && !(n.status == .proved || n.status == .generated) then
      let ev := match n.evidence with
        | some { check := some c, «by» := some b, reference := r, .. } =>
          s!" (check {c} by {b}{(r.map (s!", against " ++ ·)).getD ""})"
        | _ => ""
      IO.println s!"{n.status.name}: {id}: {n.label}{ev}"
  return 0

end tolean.Chain
