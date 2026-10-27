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
        evidence := toleanCheck "typescript-translate" "fixed corpus output and random programs" },
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

def textRef (path text : String) : FileRef :=
  { path, sha256 := sha256Hex text.toUTF8 }

/-- The manifest of a translation whose output is `outputText`. -/
def fileManifest (language : String) (target : Option String) (sources : List String)
    (output outputText module : String) : IO FileManifest := do
  let (nodes, edges) := languageChain language
  return { tolean := version, language, target, sources := ← sources.mapM fileRef
           output := textRef output outputText, module, nodes, edges }

/-- A manifest as the text of its file. -/
def manifestText (m : FileManifest) : String := (compact (Lean.toJson m)).pretty ++ "\n"

/-- Write `<output>.chain.json` for a translation that just wrote `output`. -/
def emit (language : String) (target : Option String) (sources : List String)
    (output module : String) : IO Unit := do
  let m ← fileManifest language target sources output (← IO.FS.readFile output) module
  IO.FS.writeFile (output ++ ".chain.json") (manifestText m)

/-- Record a certificate in the file manifest at `path`. Each function that
has a theorem gets a proved node. When every function has one, the translator
is proved for this file; the interpreter is then the link the proof trusts.
The certificate also proves that the parser gives the program its theorems
are about, so the printer that wrote the program is not trusted. -/
def withCertificate (m : FileManifest) (certFile certText certModule : String)
    (theorems : List (String × String)) (allFunctions : Bool) : FileManifest :=
  let axioms := ["propext", "Classical.choice", "Quot.sound"]
  let certNodes := theorems.map fun (fn, thm) =>
    ({ id := s!"certificate:{fn}", kind := "proof", status := .proved
       label := s!"{fn}: interpreter equals translation", module := some certModule
       «theorem» := some thm, axioms } : Node)
  let extra : List Node := [
    { id := "semantics", kind := "spec", status := .trusted
      label := "TypeScript semantics (interpreter)", module := some "tolean.TypeScript.Spec.Eval" },
    { id := "parsed", kind := "proof", status := .proved
      label := "the parser gives the program of the certificate", module := some certModule
      «theorem» := some s!"{certModule}.program_parsed", axioms }]
  let nodes := (m.nodes.filter fun n => !(n.id.startsWith "certificate:") && n.id != "semantics" &&
      n.id != "parsed").map fun n =>
    if n.id == "translator" && allFunctions then
      { n with status := .proved, label := n.label ++ " (certified for this file)"
               evidence := none }
    else n
  let certEdges := ("parser", "parsed") :: theorems.flatMap fun (fn, _) =>
    [("parsed", s!"certificate:{fn}"),
     ("semantics", s!"certificate:{fn}"), (s!"certificate:{fn}", "translator")]
  { m with
    nodes := nodes ++ extra ++ certNodes
    edges := (m.edges.filter fun ((a, b) : String × String) =>
      !(a.startsWith "certificate:" || b.startsWith "certificate:")) ++ certEdges
    certificate := some (textRef certFile certText) }

/-- Record a certificate in the file manifest at `path`. -/
def recordCertificate (path : System.FilePath) (certFile certModule : String)
    (theorems : List (String × String)) (allFunctions : Bool) : IO Unit := do
  let m : FileManifest ← readJson path
  writeJson path (withCertificate m certFile (← IO.FS.readFile certFile) certModule theorems allFunctions)

end tolean.Chain
