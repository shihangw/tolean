import tolean.TypeScript.Syntax.Parser
import tolean.TypeScript.Syntax.Print
import tolean.TypeScript.Translate
import tolean.Go.Syntax.Parser
import tolean.Go.Syntax.Print
import tolean.Go.Translate
import tolean.Sql.Translate
import tolean.Chain.Check
import tolean.TypeScript.Certify
import tolean.TypeScript.Interpret
import tolean.Project

/-!
The `tolean` command.

```
tolean parse [--target ES20xx] <file>
    print the syntax tree of <file>
tolean translate [--check] [--config <json>]
    build every unit that tolean.json lists, or that the inline JSON <json>
    lists; with --check, write nothing and fail when a generated file is not
    current
tolean translate-workspace
    read a workspace as JSON on stdin, {"files": [{"path", "text"}, …]} with
    tolean.json among them, and print each unit's Lean or error as JSON; it
    reads and writes no files
tolean interpret
    read TypeScript programs and calls as JSON on stdin, run each call in the
    interpreter of Spec/Eval.lean on real doubles, and print the results as
    JSON (see tolean/TypeScript/Interpret.lean); the test against Node uses it
tolean translate [--target ES20xx] [--certify] <input> <output.lean> <Namespace>
    write <input> as Lean definitions; with --certify, also write its
    certificate next to it when some function can have one (see `certify`)
tolean translate-go --root F [--root G…] [--erase-type T…] [--erase-package P…]
    <output.lean> <Namespace> <file.go>…
    write the Go functions F, G… of one package, and what they reach
tolean translate-sql <output.lean> <Namespace> --query Q [--query R…]
    --queries <file.sql>… --migrations <file.sql>…
    write the schema the queries reach (from the migrations, in order) and the queries
tolean sql-schema --table T [--table U…] --migrations <file.sql>…
    print the schema of the tables T, U… and the tables they reference
tolean certify [--target ES20xx] <input.ts> <Translated.Module> <Translated.Namespace> <output.lean> <Cert.Namespace>
    [--manifest <output>.chain.json]
    write a certificate: one theorem per function, that the interpreter and the
    translated Lean give the same result for every input; --manifest records it in
    the translation's chain manifest
tolean chain check <tolean.chain.json> [--passed check,check…]
    check that the files are unchanged, each status has evidence, and each claim
    is a theorem of exactly its spec with the recorded axioms
tolean chain graph <tolean.chain.json>
    print the verification chain as Graphviz DOT
tolean chain trust <tolean.chain.json> <claim>
    list what the claim relies on that no proof covers
```

`--target` is the ECMAScript edition the code runs on (default: ES2024). The
file extension selects the language: `.ts`, or `.go` for `parse` only.
-/

open tolean tolean.TypeScript

def usage : String :=
  "usage: tolean parse [--target ES20xx] <file.ts>\n" ++
  "       tolean translate [--check] [--config <json>]\n" ++
  "       tolean translate-workspace < workspace.json\n" ++
  "       tolean translate [--target ES20xx] [--certify] <input.ts> <output.lean> <Lean.Namespace>\n" ++
  "       tolean translate-sql <output.lean> <Lean.Namespace> --query Q --queries <file.sql>... --migrations <file.sql>...\n" ++
  "       tolean sql-schema --table T --migrations <file.sql>...\n" ++
  "       tolean translate-go --root F [--erase-type T] [--erase-package P] <output.lean> <Lean.Namespace> <file.go>...\n" ++
  "       tolean certify [--target ES20xx] <input.ts> <Translated.Module> <Translated.Namespace> <output.lean> <Cert.Namespace> [--manifest <output>.chain.json]\n" ++
  "       tolean chain check <tolean.chain.json> [--passed check,check...]\n" ++
  "       tolean chain graph <tolean.chain.json>\n" ++
  "       tolean chain trust <tolean.chain.json> <claim>\n" ++
  s!"editions: {", ".intercalate (Edition.all.map (·.name))} (default {Edition.default.name})"

def checkLanguage (path : String) : IO Bool := do
  if path.endsWith ".ts" then return true
  IO.eprintln s!"{path}: tolean reads only TypeScript (.ts) files now"
  return false

def parseGoFile (path : String) : IO UInt32 := do
  let source ← IO.FS.readFile path
  match Go.Syntax.parse source with
  | .ok f =>
    IO.println f.toSexp.render
    return 0
  | .error e =>
    IO.eprintln (e.render path)
    return 1

def parseFile (target : Edition) (path : String) : IO UInt32 := do
  if path.endsWith ".go" then return ← parseGoFile path
  unless ← checkLanguage path do return 2
  let source ← IO.FS.readFile path
  match Syntax.parse source target with
  | .ok m =>
    IO.println m.toSexp.render
    return 0
  | .error e =>
    IO.eprintln (e.render path)
    return 1

/-- Where the certificate of `output` goes: `Raise.lean` gets `RaiseCert.lean`. -/
def certPath (output : String) : String :=
  if output.endsWith ".lean" then (output.dropEnd 5).toString ++ "Cert.lean" else output ++ "Cert.lean"

/-- Write the certificate of a translation, when some function can have one,
and record it in the manifest. Remove a certificate that a former run wrote
when no function can have one now. -/
def certifyAfterTranslate (target : Edition) (input source output ns : String) : IO Unit := do
  let path := certPath output
  match Certify.certify input source ns ns (ns ++ "Cert") target with
  | .ok lean =>
    IO.FS.writeFile path lean
    let .ok (fns, all) := Certify.certifiedFunctions source target | return
    Chain.recordCertificate (output ++ ".chain.json") path (ns ++ "Cert") (ns ++ "Cert")
      (fns.map fun f => (f, s!"{ns}Cert.{f}_cert")) all
  | .error _ =>
    if ← System.FilePath.pathExists path then IO.FS.removeFile path

def translateFile (target : Edition) (input output ns : String) (certify : Bool := false) :
    IO UInt32 := do
  unless ← checkLanguage input do return 2
  let source ← IO.FS.readFile input
  match Translate.translate input source ns target with
  | .ok lean =>
    IO.FS.writeFile output lean
    Chain.emit "typescript" (some target.name) [input] output ns
    if certify then certifyAfterTranslate target input source output ns
    return 0
  | .error message =>
    IO.eprintln message
    return 1

/-- The `translate-go` options, then the output, the namespace and the files. -/
partial def translateGo (cfg : Go.Translate.Config) : List String → IO UInt32
  | "--root" :: f :: rest => translateGo { cfg with roots := cfg.roots ++ [f] } rest
  | "--erase-type" :: t :: rest =>
    translateGo { cfg with eraseTypes := cfg.eraseTypes ++ [t] } rest
  | "--erase-package" :: p :: rest =>
    translateGo { cfg with erasePackages := cfg.erasePackages ++ [p] } rest
  | output :: ns :: files@(_ :: _) => do
    let sources ← files.mapM fun (path : String) => do return (path, ← IO.FS.readFile path)
    match Go.Translate.translate sources cfg ns with
    | .ok lean =>
      IO.FS.writeFile output lean
      Chain.emit "go" none files output ns
      return 0
    | .error message =>
      IO.eprintln message
      return 1
  | _ => do
    IO.eprintln usage
    return 2

structure SqlArgs where
  queries : List String := []
  tables : List String := []
  queryFiles : List String := []
  migrations : List String := []

/-- `--queries` and `--migrations` take every path up to the next option. -/
partial def parseSqlArgs (a : SqlArgs) : List String → Except String SqlArgs
  | "--query" :: n :: rest => parseSqlArgs { a with queries := a.queries ++ [n] } rest
  | "--table" :: n :: rest => parseSqlArgs { a with tables := a.tables ++ [n] } rest
  | "--queries" :: rest =>
    let (files, rest) := rest.span (!·.startsWith "--")
    parseSqlArgs { a with queryFiles := a.queryFiles ++ files } rest
  | "--migrations" :: rest =>
    let (files, rest) := rest.span (!·.startsWith "--")
    parseSqlArgs { a with migrations := a.migrations ++ files } rest
  | x :: _ => .error s!"unexpected argument '{x}'"
  | [] => .ok a

def readAll (paths : List String) : IO (List (String × String)) :=
  paths.mapM fun (p : String) => do return (p, ← IO.FS.readFile p)

def translateSql : List String → IO UInt32
  | output :: ns :: opts => do
    match parseSqlArgs {} opts with
    | .error m =>
      IO.eprintln s!"{m}\n{usage}"
      return 2
    | .ok a =>
      match Sql.Translate.translate (← readAll a.migrations) (← readAll a.queryFiles) a.queries ns with
      | .ok lean =>
        IO.FS.writeFile output lean
        Chain.emit "sql" (some "PostgreSQL 18") (a.migrations ++ a.queryFiles) output ns
        return 0
      | .error m =>
        IO.eprintln m
        return 1
  | _ => do
    IO.eprintln usage
    return 2

def sqlSchema (opts : List String) : IO UInt32 := do
  match parseSqlArgs {} opts with
  | .error m =>
    IO.eprintln s!"{m}\n{usage}"
    return 2
  | .ok a =>
    let files ← (← readAll a.migrations).mapM fun (path, src) =>
      match Sql.parseStatements src with
      | .ok stmts => pure (path, stmts)
      | .error e => throw (IO.userError (e.render path))
    match Sql.reachTables files a.tables with
    | .ok s =>
      IO.println s.canonical
      return 0
    | .error m =>
      IO.eprintln m
      return 1

/-- Build every unit that the project config lists, or with `check`, fail when
a generated file is not current. The config is `inline` when given, else the
file `tolean.json`. -/
def translateProject (check : Bool) (inline : Option String := none) : IO UInt32 := do
  if inline.isNone then
    unless ← System.FilePath.pathExists "tolean.json" do
      IO.eprintln "no tolean.json in this directory"
      return 2
  try
    let config ← match inline with
      | some text => IO.ofExcept (Lean.Json.parse text |>.mapError (s!"--config: {·}"))
      | none => Chain.readJson (A := Lean.Json) "tolean.json"
    let writes ← Project.plan config
    let stale ← Project.apply writes check
    if check && stale > 0 then return 1
    if check then IO.println "every generated file is current"
    return 0
  catch e =>
    IO.eprintln e
    return 1

def run (target : Edition) : List String → IO UInt32
  | ["parse", path] => parseFile target path
  | ["translate"] => translateProject false
  | ["translate", "--check"] => translateProject true
  | ["translate-workspace"] => do
    IO.println (Project.workspaceJson (← (← IO.getStdin).readToEnd))
    return 0
  | ["interpret"] => do
    match TypeScript.Interpret.interpret (← (← IO.getStdin).readToEnd) with
    | .ok out => IO.println out; return 0
    | .error e => IO.eprintln e; return 1
  | ["translate", "--config", json] => translateProject false json
  | ["translate", "--check", "--config", json] => translateProject true json
  | ["translate", "--config", json, "--check"] => translateProject true json
  | ["translate", input, output, ns] => translateFile target input output ns
  | ["translate", "--certify", input, output, ns] => translateFile target input output ns true
  | "translate-sql" :: rest => translateSql rest
  | "sql-schema" :: rest => sqlSchema rest
  | "translate-go" :: rest => translateGo { roots := [], eraseTypes := [], erasePackages := [] } rest
  | "certify" :: input :: transModule :: transNs :: output :: certNs :: rest => do
    let source ← IO.FS.readFile input
    match Certify.certify input source transModule transNs certNs target with
    | .ok lean =>
      IO.FS.writeFile output lean
      if let ["--manifest", manifest] := rest then
        let .ok (fns, all) := Certify.certifiedFunctions source target | return 1
        Chain.recordCertificate manifest output certNs certNs
          (fns.map fun f => (f, s!"{certNs}.{f}_cert")) all
      return 0
    | .error e =>
      IO.eprintln e
      return 1
  | ["chain", "graph", path] => Chain.graph path
  | ["chain", "trust", path, claim] => Chain.trust path claim
  | "chain" :: "check" :: path :: rest =>
    match rest with
    | [] => Chain.check path []
    | ["--passed", list] => Chain.check path (list.splitOn ",")
    | _ => do
      IO.eprintln usage
      return 2
  | _ => do
    IO.eprintln usage
    return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | command :: "--target" :: name :: rest =>
    match Edition.parse? name with
    | some target => run target (command :: rest)
    | none =>
      IO.eprintln s!"unknown edition '{name}'\n{usage}"
      return 2
  | _ => run .default args
