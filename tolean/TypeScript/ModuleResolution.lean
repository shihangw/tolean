import tolean.TypeScript.Spec.Eval
import Lean.Data.Json
import Std.Data.HashMap

/-! Project import resolution happens before translation. The interpreter
continues to see only relative paths to concrete TypeScript files. -/
namespace tolean.TypeScript.ModuleResolution

open Lean (Json)

inductive Mode where
  | explicit
  | bundler
  | node
  deriving BEq

def mode (name : String) : Mode :=
  match name.toLower with
  | "bundler" => .bundler
  | "node16" | "nodenext" => .node
  | _ => .explicit

/-- Remove JSON comments without changing strings or line numbers. -/
def uncomment : List Char → Bool → Bool → List Char
  | [], _, _ => []
  | c :: cs, true, true => c :: uncomment cs true false
  | '\\' :: cs, true, false => '\\' :: uncomment cs true true
  | '"' :: cs, quoted, false => '"' :: uncomment cs (!quoted) false
  | '/' :: '/' :: cs, false, false => line cs
  | '/' :: '*' :: cs, false, false => block cs
  | c :: cs, quoted, escaped => c :: uncomment cs quoted escaped
where
  line : List Char → List Char
    | [] => []
    | '\n' :: cs => '\n' :: uncomment cs false false
    | _ :: cs => ' ' :: line cs
  block : List Char → List Char
    | [] => ['/', '*']
    | '*' :: '/' :: cs => ' ' :: ' ' :: uncomment cs false false
    | c :: cs => (if c == '\n' then '\n' else ' ') :: block cs

/-- JSONC permits a comma before a closing brace or bracket. -/
def uncomma : List Char → Bool → Bool → List Char
  | [], _, _ => []
  | c :: cs, true, true => c :: uncomma cs true false
  | '\\' :: cs, true, false => '\\' :: uncomma cs true true
  | '"' :: cs, quoted, false => '"' :: uncomma cs (!quoted) false
  | ',' :: cs, false, false =>
    let next := (cs.dropWhile Char.isWhitespace).head?
    (if next == some '}' || next == some ']' then ' ' else ',') :: uncomma cs false false
  | c :: cs, quoted, escaped => c :: uncomma cs quoted escaped

/-- Parse each config before merging, so an invalid base is not hidden by a child. -/
def parseConfig (path text : String) : Except String Json := do
  let j ← (Json.parse (String.ofList (uncomma (uncomment text.toList false false) false false))).mapError
    (s!"{path}: {·}")
  unless j matches .obj _ do throw s!"{path}: expected an object"
  if let .ok o := j.getObjVal? "compilerOptions" then
    unless o matches .obj _ do throw s!"{path}: compilerOptions must be an object"
  return j

/-- Config paths are relative to the declaring config, never to its child.
The workspace boundary is shared by the native and browser hosts. -/
def basePath (files : List String) (path base : String) : Except String String := do
  unless base.startsWith "./" || base.startsWith "../" do
    throw s!"{path}: package or absolute extends '{base}' is not supported; use a relative config inside the project"
  if base.any fun c => c == '\\' || c == '$' then
    throw s!"{path}: unsupported extends path '{base}'"
  let some parts := Eval.normalizeSegments (path.splitOn "/").dropLast (base.splitOn "/")
    | throw s!"{path}: extends '{base}' leaves the project"
  let name := "/".intercalate parts
  if files.contains name then return name
  if !name.endsWith ".json" && files.contains (name ++ ".json") then return name ++ ".json"
  throw s!"{path}: extends '{base}' has no config file"

-- Only completed configs enter the cache. The separate active stack still
-- detects cycles, while shared ancestors are read and merged once.
private def loadOptionsCached {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (files : List String) (read : String → m String) :
    Nat → List String → String → StateT (Std.HashMap String Json) m Json
  | 0, _, path => throw s!"{path}: config inheritance exceeds the workspace file count"
  | fuel + 1, stack, path => do
    if stack.contains path then
      throw s!"{path}: config extends cycle: {" -> ".intercalate (stack.reverse ++ [path])}"
    if let some options := (← get)[path]? then return options
    let j ← match parseConfig path (← liftM (read path)) with
      | .ok j => pure j
      | .error e => throw e
    let bases ← match (j.getObjVal? "extends").toOption with
      | none => pure []
      | some (.str s) => pure [s]
      | some (.arr xs) => xs.toList.mapM fun x => match x with
        | .str s => pure s
        | _ => throw s!"{path}: extends must be a string or an array of strings"
      | some _ => throw s!"{path}: extends must be a string or an array of strings"
    let mut options := Json.mkObj []
    for base in bases do
      let target ← match basePath files path base with
        | .ok target => pure target
        | .error e => throw e
      let inherited ← loadOptionsCached files read fuel (path :: stack) target
      options := options.mergeObj inherited
    options := options.mergeObj ((j.getObjVal? "compilerOptions").toOption.getD (Json.mkObj []))
    modify (·.insert path options)
    return options

/-- Merge the compiler options that import resolution consumes. Each base
starts independently, and later bases replace earlier options. Path-valued
options are not consumed: imports remain relative to their source files.
The cache belongs to one load, so subsequent loads read fresh config text. -/
def loadOptions {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (files : List String) (read : String → m String)
    (fuel : Nat) (stack : List String) (path : String) : m Json :=
  (loadOptionsCached files read fuel stack path).run' {}

/-- A merged tsconfig takes precedence over the fallback. -/
def setting (tsconfig : Option Json) (fallback : Option String) : Except String Mode := do
  match tsconfig with
  | none => return mode (fallback.getD "")
  | some options =>
    for key in ["moduleSuffixes", "rootDirs"] do
      if (options.getObjVal? key).isOk then
        throw s!"tsconfig.json: {key} is not supported for import resolution"
    let value := (options.getObjVal? "moduleResolution").toOption
    match value with
    | none => return .explicit
    | some (.str name) => return mode name
    | some _ => throw "tsconfig.json: compilerOptions.moduleResolution must be a string"

/-- Resolve against every workspace file, not just translated sources. This
keeps a missing source entry from changing which candidate wins. -/
def resolve (m : Mode) (files : List String) (file source : String) : Except String String := do
  let fail := s!"{file}: '{source}' is not a supported relative TypeScript import"
  if source.any fun c => c == '%' || c == '?' || c == '#' || c == '\\' then throw fail
  let parts := source.splitOn "/"
  unless parts.head? == some "." || parts.head? == some ".." do throw fail
  let raw := parts.getLast!
  if raw.isEmpty || raw == "." || raw == ".." then throw fail
  if raw.endsWith ".d.ts" || raw.endsWith ".tsx" then
    throw s!"{fail}; .tsx and declaration files are refused"
  if raw.endsWith ".ts" then
    let some path := Eval.resolvePath file source | throw fail
    return path
  let candidates ← match m with
    | .bundler =>
      if raw.endsWith ".js" && raw != ".js" then
        pure [(source.dropEnd 3).toString ++ ".ts"]
      else
        if raw.contains '.' then throw s!"{fail}; only extensionless, .js and .ts imports are supported"
        pure [source ++ ".ts", source ++ "/index.ts"]
    | .node =>
      unless raw.endsWith ".js" && raw != ".js" do
        throw s!"{fail}; node16 and nodenext require .js or .ts"
      pure [(source.dropEnd 3).toString ++ ".ts"]
    | .explicit => throw s!"{fail}; this resolution mode requires .ts"
  for candidate in candidates do
    if candidate == source ++ "/index.ts" then
      -- TypeScript tries these files before a directory. Do not silently
      -- choose index.ts when TypeScript would choose an unsupported target.
      for suffix in [".tsx", ".d.ts", ".js", ".jsx", "/package.json"] do
        if let some base := Eval.resolvePath file (source ++ ".ts") then
          let path := (base.dropEnd 3).toString ++ suffix
          if files.contains path then
            throw s!"{file}: '{source}' resolves through unsupported file '{path}' before index.ts"
    if let some path := Eval.resolvePath file candidate then
      if path.endsWith ".d.ts" then throw s!"{fail}; declaration files are refused"
      if files.contains path then return path
  throw s!"{file}: '{source}' has no supported .ts target"

end tolean.TypeScript.ModuleResolution
