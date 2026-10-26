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

/-- One translation unit, with its resolved settings: a TypeScript file, a Go
  package or a SQL query file. -/
inductive Job where
  | typescript (settings : Json) (source : String)
  | go (settings : Json) (files : List String)
  | sql (settings : Json) (queryFile : String) (migrations : List String)

/-- The units that the project file asks for, given every file in the project. -/
def units (config : Json) (files : List String) : List Job := Id.run do
  let mut out : List Job := []
  if let .ok ts := config.getObjVal? "typescript" then
    for f in expand files (strings ts "sources") do
      out := out ++ [.typescript (settings ts [f]) f]
  if let .ok go := config.getObjVal? "go" then
    let matched := expand files (strings go "sources")
    for dir in (matched.map dirOf).eraseDups do
      let pkg := matched.filter (dirOf · == dir)
      out := out ++ [.go (settings go pkg) pkg]
  if let .ok sql := config.getObjVal? "sql" then
    for f in expand files (strings sql "sources") do
      let s := settings sql [f]
      out := out ++ [.sql s f (expand files (strings s "migrations"))]
  return out

/-- The files that a unit reads. -/
def Job.sources : Job → List String
  | .typescript _ f => [f]
  | .go _ fs => fs
  | .sql _ f ms => ms ++ [f]

/-- A unit's translation: the output path, its namespace and the Lean text. -/
structure Translation where
  output : String
  ns : String
  lean : String

/-- The names of the sqlc queries in a file: each `-- name: X` line. -/
def queryNames (text : String) : List String :=
  (text.splitOn "\n").filterMap fun line =>
    match (line.trimAscii.toString.splitOn " ").filter (· != "") with
    | "--" :: "name:" :: n :: _ => some n
    | _ => none

/-- Translate one unit, given the text of each file it reads. This does no IO,
so the playground runs it in the browser. -/
def translateUnit (u : Job) (read : String → Except String String) : Except String Translation := do
  match u with
  | .typescript s source =>
    let output := (string? s "output").getD s!"{dirOf source}{(stem source).capitalize}.lean"
    let ns := (string? s "namespace").getD (namespaceOf output)
    let targetName := (string? s "target").getD TypeScript.Edition.default.name
    let some target := TypeScript.Edition.parse? targetName
      | throw s!"{source}: unknown target '{targetName}'"
    let lean ← TypeScript.Translate.translate source (← read source) ns target
    return { output, ns, lean }
  | .go s files =>
    let dir := dirOf (files.head!)
    let pkgName := ((segments dir).getLast?).getD "Package"
    let output := (string? s "output").getD s!"{dir}{pkgName.capitalize}.lean"
    let ns := (string? s "namespace").getD (namespaceOf output)
    let sources ← files.mapM fun f => return (f, ← read f)
    let roots ← match strings s "roots" with
      | [] => Go.Translate.exportedFunctions sources
      | rs => pure rs
    let cfg : Go.Translate.Config :=
      { roots, eraseTypes := strings s "eraseTypes", erasePackages := strings s "erasePackages" }
    return { output, ns, lean := ← Go.Translate.translate sources cfg ns }
  | .sql s queryFile migrations =>
    let output := (string? s "output").getD s!"{dirOf queryFile}{(stem queryFile).capitalize}.lean"
    let ns := (string? s "namespace").getD (namespaceOf output)
    let text ← read queryFile
    let queries := match strings s "queries" with
      | [] => queryNames text
      | qs => qs
    let migrationTexts ← migrations.mapM fun f => return (f, ← read f)
    return { output, ns, lean := ← Sql.Translate.translate migrationTexts [(queryFile, text)] queries ns }

/-- The language name and target that a unit's manifest records. -/
def Job.chainLanguage : Job → String × Option String
  | .typescript s _ =>
    ("typescript", some ((string? s "target").getD TypeScript.Edition.default.name))
  | .go .. => ("go", none)
  | .sql .. => ("sql", some "PostgreSQL 18")

/-- What one unit writes: its Lean file and manifest, and for a TypeScript
file with `certify`, its certificate. -/
def unitWrites (u : Job) : IO (List Write) := do
  let texts ← u.sources.mapM fun (f : String) => do return (f, ← IO.FS.readFile f)
  let read (f : String) : Except String String :=
    match texts.lookup f with
    | some t => .ok t
    | none => .error s!"{f}: not read"
  let t ← ok (translateUnit u read)
  let (language, target) := u.chainLanguage
  let m ← Chain.fileManifest language target u.sources t.output t.lean t.ns
  let lean := [Write.file t.output t.lean]
  match u with
  | .typescript s source =>
    if !bool s "certify" false then
      return lean ++ [.file (t.output ++ ".chain.json") (Chain.manifestText m)]
    let some target := TypeScript.Edition.parse? (target.getD "")
      | return lean ++ [.file (t.output ++ ".chain.json") (Chain.manifestText m)]
    let text ← ok (read source)
    let cert := certPath t.output
    match TypeScript.Certify.certify source text t.ns t.ns (t.ns ++ "Cert") target with
    | .ok certText =>
      let (fns, all) ← ok (TypeScript.Certify.certifiedFunctions text target)
      let m := Chain.withCertificate m cert certText (t.ns ++ "Cert")
        (fns.map fun f => (f, s!"{t.ns}Cert.{f}_cert")) all
      return lean ++ [.file cert certText, .file (t.output ++ ".chain.json") (Chain.manifestText m)]
    | .error _ =>
      return lean ++ [.file (t.output ++ ".chain.json") (Chain.manifestText m), .remove cert]
  | _ => return lean ++ [.file (t.output ++ ".chain.json") (Chain.manifestText m)]

/-- What the project file asks for: every file to write or to remove. Paths
are relative to the project root, which must be the working directory. -/
def plan (config : Json) : IO (List Write) := do
  let files ← projectFiles "."
  return (← (units config files).mapM unitWrites).flatten

/-! ### Workspaces as JSON

`tolean translate-workspace` and the playground's WebAssembly build take a
whole workspace as JSON, `{"files": [{"path", "text"}, …]}` with
`tolean.json` among the files, and return each unit's result:
`{"units": [{"output", "lean"} or {"sources", "error"}, …]}`, or `{"error"}`
when the workspace has no valid `tolean.json`. One unit's error does not hide
the others, and nothing here reads or writes files. -/

def unitJson (texts : List (String × String)) (job : Job) : Json :=
  let read (f : String) : Except String String :=
    match texts.lookup f with
    | some t => .ok t
    | none => .error s!"{f}: no such file"
  match translateUnit job read with
  | .ok t => Json.mkObj [("output", t.output), ("lean", t.lean)]
  | .error e => Json.mkObj [("sources", Lean.toJson job.sources), ("error", e)]

def translateWorkspace (input : String) : Except String Json := do
  let ws ← Json.parse input
  let files ← ws.getObjValAs? (List Json) "files"
  let texts ← files.mapM fun f => do
    return ((← f.getObjValAs? String "path"), (← f.getObjValAs? String "text"))
  let some configText := texts.lookup "tolean.json"
    | throw "the workspace has no tolean.json"
  let config ← (Json.parse configText).mapError (s!"tolean.json: {·}")
  let jobs := units config (texts.map (·.1))
  return Json.mkObj [("units", Json.arr (jobs.map (unitJson texts)).toArray)]

/-- `translateWorkspace` as JSON text, with an error as `{"error"}`. -/
def workspaceJson (input : String) : String :=
  match translateWorkspace input with
  | .ok j => j.compress
  | .error e => (Json.mkObj [("error", e)]).compress

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
