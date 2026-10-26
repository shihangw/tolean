import Lean.Data.Json
import Std.Data.TreeMap.Raw

/-!
Chain manifests: the verification chain of translated code, as data.

A file manifest sits next to each generated Lean file, as
`<output>.chain.json`. The translator writes it. It names the source and the
output with their SHA-256 hashes, and lists the links of the chain from the
source to the output and from the source to what runs: each link is a node
with a status and the evidence for that status.

A project manifest, `tolean.chain.json`, is written by people. It lists the
file manifests, the project's own links (contracts, glue code, proofs that
join languages), its claims, and its assumptions.

`tolean chain check` checks both, `tolean chain graph` draws them, and
`tolean chain trust` lists what a claim relies on.
-/
namespace tolean.Chain

open Lean (Json ToJson FromJson toJson fromJson?)

inductive Status where
  /-- Checked by the Lean kernel. -/
  | proved
  /-- Trusted, with a check that compares it with a reference. -/
  | tested
  /-- Trusted, without such a check. -/
  | trusted
  /-- A statement people read and agree to, such as a claim or a contract. -/
  | readByPeople
  /-- Produced by a tool, such as the generated Lean. -/
  | generated
  /-- Not built yet. -/
  | planned
deriving BEq, Repr, Inhabited, DecidableEq

def Status.name : Status → String
  | .proved => "proved"
  | .tested => "tested"
  | .trusted => "trusted"
  | .readByPeople => "read-by-people"
  | .generated => "generated"
  | .planned => "planned"

def Status.all : List Status := [.proved, .tested, .trusted, .readByPeople, .generated, .planned]

instance : ToJson Status := ⟨fun s => .str s.name⟩
instance : FromJson Status where
  fromJson? j := do
    let s ← j.getStr?
    match Status.all.find? (·.name == s) with
    | some st => .ok st
    | none => .error s!"unknown status '{s}'"

/-- Why a node has its status. -/
structure Evidence where
  /-- The check that compares it with a reference, such as `go-check`. -/
  check : Option String := none
  /-- Who runs the check: `tolean` (tolean's own CI, for this tolean version)
  or `project` (the project's CI, which reports it to `chain check`). -/
  «by» : Option String := none
  /-- What the check compares against, such as `go/parser`. -/
  reference : Option String := none
deriving ToJson, FromJson, Inhabited, Repr

structure Node where
  id : String
  /-- `parser`, `translator`, `spec`, `runtime`, `proof`, `contract`, `glue`,
  `model` or `claim`. -/
  kind : String
  status : Status
  /-- A short description, for people and for the graph. -/
  label : String
  /-- The Lean module, for a spec or a proof. -/
  module : Option String := none
  /-- The theorem, for a proved node. -/
  «theorem» : Option String := none
  /-- The axioms the theorem may depend on, for a proved node. -/
  axioms : List String := []
  evidence : Option Evidence := none
  note : Option String := none
deriving ToJson, Inhabited, Repr

/-- A missing optional field reads as its default. -/
def optField {A : Type} [FromJson A] (j : Json) (k : String) (d : A) : Except String A :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok d
  | .ok v => fromJson? v

instance : FromJson Node where
  fromJson? j := do
    return { id := ← j.getObjValAs? String "id", kind := ← j.getObjValAs? String "kind"
             status := ← j.getObjValAs? Status "status", label := ← j.getObjValAs? String "label"
             module := ← optField j "module" none, «theorem» := ← optField j "theorem" none
             axioms := ← optField j "axioms" [], evidence := ← optField j "evidence" none
             note := ← optField j "note" none }

structure FileRef where
  path : String
  sha256 : String
deriving ToJson, FromJson, Inhabited, Repr

structure FileManifest where
  tolean : String
  language : String
  target : Option String := none
  sources : List FileRef
  output : FileRef
  /-- The Lean module, which is the namespace of the generated code. -/
  module : String
  nodes : List Node
  /-- Edges between node ids; `source` and `output` stand for the files. -/
  edges : List (String × String)
deriving ToJson, FromJson, Inhabited, Repr

structure Claim where
  id : String
  /-- The claim, a `def … : Prop`. -/
  spec : String
  /-- The theorem whose type is exactly the claim. -/
  proof : String
  /-- The module that holds the proof; `chain check` imports it. -/
  module : String
  /-- The axioms the proof may depend on. -/
  axioms : List String
  /-- Generated modules and project nodes the claim relies on. -/
  depends : List String
deriving ToJson, FromJson, Inhabited, Repr

structure ProjectManifest where
  /-- Paths of file manifests, relative to the project manifest. -/
  files : List String
  nodes : List Node := []
  /-- Edges between project node ids and generated modules. -/
  edges : List (String × String) := []
  claims : List Claim
  assumptions : List String := []
deriving ToJson, Inhabited, Repr

instance : FromJson ProjectManifest where
  fromJson? j := do
    return { files := ← j.getObjValAs? (List String) "files"
             nodes := ← optField j "nodes" [], edges := ← optField j "edges" []
             claims := ← optField j "claims" [], assumptions := ← optField j "assumptions" [] }

def readJson {A : Type} [FromJson A] (path : System.FilePath) : IO A := do
  let text ← IO.FS.readFile path
  match Json.parse text >>= fromJson? with
  | .ok v => return v
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- Leave out null fields and empty lists, so a manifest says only what holds. -/
partial def compact : Json → Json
  | .obj kvs => .obj (kvs.foldl (init := {}) fun acc k v =>
      match v with
      | .null | .arr #[] => acc
      | v => acc.insert k (compact v))
  | .arr xs => .arr (xs.map compact)
  | j => j

def writeJson {A : Type} [ToJson A] (path : System.FilePath) (v : A) : IO Unit :=
  IO.FS.writeFile path ((compact (toJson v)).pretty ++ "\n")

end tolean.Chain
