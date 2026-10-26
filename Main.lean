import tolean.TypeScript.Syntax.Parser
import tolean.TypeScript.Syntax.Print
import tolean.TypeScript.Translate
import tolean.Go.Syntax.Parser
import tolean.Go.Syntax.Print
import tolean.Go.Translate
import tolean.Sql.Translate
import tolean.Chain.Check
import tolean.TypeScript.Certify

/-!
The `tolean` command.

```
tolean parse [--target ES20xx] <file>
    print the syntax tree of <file>
tolean translate [--target ES20xx] <input> <output.lean> <Namespace>
    write <input> as Lean definitions
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
  "       tolean translate [--target ES20xx] <input.ts> <output.lean> <Lean.Namespace>\n" ++
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

def translateFile (target : Edition) (input output ns : String) : IO UInt32 := do
  unless ← checkLanguage input do return 2
  let source ← IO.FS.readFile input
  match Translate.translate input source ns target with
  | .ok lean =>
    IO.FS.writeFile output lean
    Chain.emit "typescript" (some target.name) [input] output ns
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

def run (target : Edition) : List String → IO UInt32
  | ["parse", path] => parseFile target path
  | ["translate", input, output, ns] => translateFile target input output ns
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
        Chain.recordCertificate manifest output certNs
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
