import tolean.Chain.Manifest
import tolean.Chain.Sha256
import tolean.Version

/-!
The chain each translator writes next to its output. The nodes say what the
translation relies on; Tolean's own CI runs the checks named `by: tolean`.
-/
namespace tolean.Chain

def fileRef (path : String) : IO FileRef := do
  return { path, sha256 := sha256Hex (← IO.FS.readBinFile path) }

private def toleanCheck (check reference : String) : Option Evidence :=
  some { check := some check, «by» := some "tolean", reference := some reference }

/-- The links of one language's chain, from the source to what runs. -/
def languageChain : String → List Node × List (String × String)
  | "typescript" =>
    ([{ id := "parser", kind := "parser", status := .tested, label := "TypeScript parser"
        evidence := toleanCheck "typescript-parse" "tsc" },
      { id := "translator", kind := "translator", status := .tested, label := "TypeScript translator"
        evidence := toleanCheck "typescript-translate" "tsc-based translator" },
      { id := "spec", kind := "spec", status := .tested, label := "JavaScript number laws"
        module := some "tolean.TypeScript.Spec.Number"
        evidence := toleanCheck "typescript-engines" "Node 22 and 24" },
      { id := "runtime", kind := "runtime", status := .trusted, label := "JavaScript engine" }],
     [("source", "parser"), ("parser", "translator"), ("translator", "output"),
      ("spec", "output"), ("runtime", "output")])
  | "go" =>
    ([{ id := "parser", kind := "parser", status := .tested, label := "Go parser"
        evidence := toleanCheck "go-check" "go/parser" },
      { id := "translator", kind := "translator", status := .tested, label := "Go translator"
        evidence := toleanCheck "go-check" "fixed corpus output" },
      { id := "spec", kind := "spec", status := .trusted, label := "Go Spec"
        module := some "tolean.Go.Spec.Basic" },
      { id := "runtime", kind := "runtime", status := .trusted, label := "Go compiler" }],
     [("source", "parser"), ("parser", "translator"), ("translator", "output"),
      ("spec", "output"), ("runtime", "output")])
  | _ =>
    ([{ id := "parser", kind := "parser", status := .tested, label := "SQL parser"
        evidence := toleanCheck "sql-corpus" "PostgreSQL 18" },
      { id := "translator", kind := "translator", status := .tested, label := "SQL translator"
        evidence := toleanCheck "sql-corpus" "PostgreSQL 18" },
      { id := "spec", kind := "spec", status := .tested, label := "Postgres Spec"
        module := some "tolean.Sql.Spec.Basic"
        evidence := toleanCheck "sql-corpus" "PostgreSQL 18" },
      { id := "isolation", kind := "model", status := .tested, label := "READ COMMITTED model"
        module := some "tolean.Sql.Spec.ReadCommitted"
        evidence := toleanCheck "sql-corpus" "PostgreSQL 18" },
      { id := "runtime", kind := "runtime", status := .trusted, label := "PostgreSQL server" }],
     [("source", "parser"), ("parser", "translator"), ("translator", "output"),
      ("spec", "output"), ("isolation", "output"), ("runtime", "output")])

/-- Write `<output>.chain.json` for a translation that just wrote `output`. -/
def emit (language : String) (target : Option String) (sources : List String)
    (output module : String) : IO Unit := do
  let (nodes, edges) := languageChain language
  writeJson (output ++ ".chain.json") ({
    tolean := version, language, target
    sources := ← sources.mapM fileRef, output := ← fileRef output
    module, nodes, edges } : FileManifest)

/-- Record a certificate in the file manifest at `path`. Each function that
has a theorem gets a proved node. When every function has one, the translator
is proved for this file; the interpreter and the term printer are then the
links the proof trusts. -/
def recordCertificate (path : System.FilePath) (certFile certModule : String)
    (theorems : List (String × String)) (allFunctions : Bool) : IO Unit := do
  let m : FileManifest ← readJson path
  let axioms := ["propext", "Classical.choice", "Quot.sound"]
  let certNodes := theorems.map fun (fn, thm) =>
    ({ id := s!"certificate:{fn}", kind := "proof", status := .proved
       label := s!"{fn}: interpreter equals translation", module := some certModule
       «theorem» := some thm, axioms } : Node)
  let extra : List Node := [
    { id := "semantics", kind := "spec", status := .trusted
      label := "TypeScript semantics (interpreter)", module := some "tolean.TypeScript.Spec.Eval" },
    { id := "term-printer", kind := "translator", status := .trusted
      label := "syntax tree printed as a Lean term" }]
  let nodes := (m.nodes.filter fun n => !(n.id.startsWith "certificate:") && n.id != "semantics" &&
      n.id != "term-printer").map fun n =>
    if n.id == "translator" && allFunctions then
      { n with status := .proved, label := n.label ++ " (certified for this file)"
               evidence := none }
    else n
  let certEdges := theorems.flatMap fun (fn, _) =>
    [("parser", s!"certificate:{fn}"), ("term-printer", s!"certificate:{fn}"),
     ("semantics", s!"certificate:{fn}"), (s!"certificate:{fn}", "translator")]
  writeJson path { m with
    nodes := nodes ++ extra ++ certNodes
    edges := (m.edges.filter fun ((a, b) : String × String) => !(a.startsWith "certificate:" || b.startsWith "certificate:")) ++ certEdges
    certificate := some (← fileRef certFile) }

end tolean.Chain
