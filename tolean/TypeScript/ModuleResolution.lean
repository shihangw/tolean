import tolean.TypeScript.Spec.Eval
import Lean.Data.Json

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

/-- A tsconfig next to tolean.json takes precedence over the fallback.
Inherited resolution options are refused rather than guessed. -/
def setting (tsconfig : Option String) (fallback : Option String) : Except String Mode := do
  match tsconfig with
  | none => return mode (fallback.getD "")
  | some text =>
    let j ← (Json.parse (String.ofList (uncomma (uncomment text.toList false false) false false))).mapError
      (s!"tsconfig.json: {·}")
    unless j matches .obj _ do throw "tsconfig.json: expected an object"
    if (j.getObjVal? "extends").isOk then
      throw "tsconfig.json: inherited moduleResolution and other resolution options are not supported; use a standalone tsconfig.json"
    let options := (j.getObjVal? "compilerOptions").toOption
    if let some o := options then
      unless o matches .obj _ do throw "tsconfig.json: compilerOptions must be an object"
      if (o.getObjVal? "moduleSuffixes").isOk then
        throw "tsconfig.json: moduleSuffixes is not supported for import resolution"
    let value := options.bind fun o => (o.getObjVal? "moduleResolution").toOption
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
