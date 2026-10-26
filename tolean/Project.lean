import tolean.Chain.Emit
import tolean.TypeScript.Translate
import tolean.TypeScript.Certify
import tolean.Go.Translate
import tolean.Sql.Translate

/-!
The project file, `tolean.json`. It lists what to translate, so that
`tolean translate` builds a whole project without file names on the command
line.

Each language has an object. Its settings apply to every source, `sources`
lists globs, and `overrides` changes settings for the files its own `sources`
match. Each language groups the matched files into the unit it translates: a
TypeScript file, a Go package (the files of one directory), or a SQL query
file. Settings resolve per unit: first the language's own, then each
override that matches one of the unit's files, in order, so the last value
wins.

A glob is a path in which `*` matches within one directory and `**` matches
any number of directories. Files are taken in sorted order, so migrations
replay in order.
-/
namespace tolean.Project

open Lean (Json)

/-! ### Globs -/

/-- `*` in one path segment matches any run of characters. -/
partial def segmentMatch (pat name : List Char) : Bool :=
  match pat, name with
  | [], [] => true
  | '*' :: ps, ns => segmentMatch ps ns || (match ns with | _ :: rest => segmentMatch pat rest | [] => false)
  | p :: ps, n :: ns => p == n && segmentMatch ps ns
  | _, _ => false

/-- `**` matches any number of segments. -/
partial def globMatch : List String → List String → Bool
  | [], [] => true
  | "**" :: ps, segs => globMatch ps segs || (match segs with | _ :: rest => globMatch ("**" :: ps) rest | [] => false)
  | p :: ps, s :: segs => segmentMatch p.toList s.toList && globMatch ps segs
  | _, _ => false

def segments (path : String) : List String :=
  (path.splitOn "/").filter (· != "") |>.filter (· != ".")

def fits (glob path : String) : Bool := globMatch (segments glob) (segments path)

/-- Every file under the project root, as a relative path, without build and
tool directories. -/
def projectFiles (root : System.FilePath) : IO (List String) := do
  let skip := [".lake", ".git", "node_modules"]
  let all ← root.walkDir fun p => return !skip.contains (p.fileName.getD "")
  let rootStr := root.toString
  let rel := all.toList.filterMap fun (p : System.FilePath) =>
    let s := p.toString
    let s := if s.startsWith (rootStr ++ "/") then (s.drop (rootStr.length + 1)).toString else s
    if s.startsWith "./" then some (s.drop 2).toString else some (s : String)
  rel.filterMapM fun (s : String) => do
    if ← (root / s).isDir then return none else return some s

/-- The files that `globs` match, sorted and without duplicates. -/
def expand (files : List String) (globs : List String) : List String :=
  (files.filter fun f => globs.any (fits · f)).mergeSort (· < ·) |>.eraseDups

/-! ### Settings -/

def strings (j : Json) (key : String) : List String :=
  (j.getObjValAs? (List String) key).toOption.getD []

def string? (j : Json) (key : String) : Option String := (j.getObjValAs? String key).toOption

def bool (j : Json) (key : String) (default : Bool) : Bool :=
  (j.getObjValAs? Bool key).toOption.getD default

/-- The settings of a unit whose files are `unitFiles`. -/
def settings (lang : Json) (unitFiles : List String) : Json := Id.run do
  let strip (j : Json) : Json := match j with
    | .obj kvs => .obj ((kvs.erase "sources").erase "overrides")
    | j => j
  let mut s := strip lang
  let overrides := (lang.getObjValAs? (List Json) "overrides").toOption.getD []
  for o in overrides do
    if unitFiles.any fun f => (strings o "sources").any (fits · f) then
      s := s.mergeObj (strip o)
  return s

/-! ### Units -/

def capitalize (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

def dirOf (path : String) : String :=
  match (segments path).dropLast with
  | [] => ""
  | ds => "/".intercalate ds ++ "/"

def stem (path : String) : String :=
  let name := ((segments path).getLast?).getD path
  ((name.splitOn ".").head?).getD name

/-- `src/sensor/Raise.lean` has the namespace `src.sensor.Raise`. -/
def namespaceOf (output : String) : String :=
  ".".intercalate (segments ((output.dropEnd 5).toString))

/-- One file to write, or one to remove because it is stale. -/
inductive Write where
  | file (path text : String)
  | remove (path : String)

def certPath (output : String) : String := (output.dropEnd 5).toString ++ "Cert.lean"

def ok {A : Type} (e : Except String A) : IO A :=
  match e with
  | .ok v => return v
  | .error m => throw (IO.userError m)

def typescriptUnit (s : Json) (source : String) : IO (List Write) := do
  let output := (string? s "output").getD s!"{dirOf source}{capitalize (stem source)}.lean"
  let ns := (string? s "namespace").getD (namespaceOf output)
  let targetName := (string? s "target").getD TypeScript.Edition.default.name
  let some target := TypeScript.Edition.parse? targetName
    | throw (IO.userError s!"{source}: unknown target '{targetName}'")
  let text ← IO.FS.readFile source
  let lean ← ok (TypeScript.Translate.translate source text ns target)
  let m ← Chain.fileManifest "typescript" (some target.name) [source] output lean ns
  if !bool s "certify" false then
    return [.file output lean, .file (output ++ ".chain.json") (Chain.manifestText m)]
  let cert := certPath output
  match TypeScript.Certify.certify source text ns ns (ns ++ "Cert") target with
  | .ok certText =>
    let (fns, all) ← ok (TypeScript.Certify.certifiedFunctions text target)
    let m := Chain.withCertificate m cert certText (ns ++ "Cert")
      (fns.map fun f => (f, s!"{ns}Cert.{f}_cert")) all
    return [.file output lean, .file cert certText, .file (output ++ ".chain.json") (Chain.manifestText m)]
  | .error _ =>
    return [.file output lean, .file (output ++ ".chain.json") (Chain.manifestText m), .remove cert]

def goUnit (s : Json) (files : List String) : IO (List Write) := do
  let dir := dirOf (files.head!)
  let pkgName := ((segments dir).getLast?).getD "Package"
  let output := (string? s "output").getD s!"{dir}{capitalize pkgName}.lean"
  let ns := (string? s "namespace").getD (namespaceOf output)
  let sources ← files.mapM fun (f : String) => do return (f, ← IO.FS.readFile f)
  let roots ← match strings s "roots" with
    | [] => ok (Go.Translate.exportedFunctions sources)
    | rs => pure rs
  let cfg : Go.Translate.Config :=
    { roots, eraseTypes := strings s "eraseTypes", erasePackages := strings s "erasePackages" }
  let lean ← ok (Go.Translate.translate sources cfg ns)
  let m ← Chain.fileManifest "go" none files output lean ns
  return [.file output lean, .file (output ++ ".chain.json") (Chain.manifestText m)]

/-- The names of the sqlc queries in a file: each `-- name: X` line. -/
def queryNames (text : String) : List String :=
  (text.splitOn "\n").filterMap fun line =>
    match (line.trimAscii.toString.splitOn " ").filter (· != "") with
    | "--" :: "name:" :: n :: _ => some n
    | _ => none

def sqlUnit (allFiles : List String) (s : Json) (queryFile : String) : IO (List Write) := do
  let output := (string? s "output").getD s!"{dirOf queryFile}{capitalize (stem queryFile)}.lean"
  let ns := (string? s "namespace").getD (namespaceOf output)
  let migrations := expand allFiles (strings s "migrations")
  let text ← IO.FS.readFile queryFile
  let queries := match strings s "queries" with
    | [] => queryNames text
    | qs => qs
  let migrationTexts ← migrations.mapM fun (f : String) => do return (f, ← IO.FS.readFile f)
  let lean ← ok (Sql.Translate.translate migrationTexts [(queryFile, text)] queries ns)
  let m ← Chain.fileManifest "sql" (some "PostgreSQL 18") (migrations ++ [queryFile]) output lean ns
  return [.file output lean, .file (output ++ ".chain.json") (Chain.manifestText m)]

/-- What the project file asks for: every file to write or to remove. Paths
are relative to the project root, which must be the working directory. -/
def plan (config : Json) : IO (List Write) := do
  let files ← projectFiles "."
  let mut out : List Write := []
  if let .ok ts := config.getObjVal? "typescript" then
    for f in expand files (strings ts "sources") do
      out := out ++ (← typescriptUnit (settings ts [f]) f)
  if let .ok go := config.getObjVal? "go" then
    let matched := expand files (strings go "sources")
    for dir in (matched.map dirOf).eraseDups do
      let pkg := matched.filter (dirOf · == dir)
      out := out ++ (← goUnit (settings go pkg) pkg)
  if let .ok sql := config.getObjVal? "sql" then
    for f in expand files (strings sql "sources") do
      out := out ++ (← sqlUnit files (settings sql [f]) f)
  return out

/-- Write the plan, or with `check`, report each file that differs and write
nothing. Returns the number of stale files. -/
def apply (writes : List Write) (check : Bool) : IO Nat := do
  let mut stale := 0
  for w in writes do
    match w with
    | .file path text =>
      let current ← if ← System.FilePath.pathExists path then some <$> IO.FS.readFile path else pure none
      if current != some text then
        if check then
          IO.eprintln s!"{path} is not current; run tolean translate"
          stale := stale + 1
        else
          if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
          IO.FS.writeFile path text
    | .remove path =>
      if ← System.FilePath.pathExists path then
        if check then
          IO.eprintln s!"{path} is stale; run tolean translate"
          stale := stale + 1
        else IO.FS.removeFile path
  return stale

end tolean.Project
