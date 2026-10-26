import tolean.Project

/-!
The entry point into the translator for the playground and the npm package.
`build.sh` compiles it to WebAssembly, and both call it through `glue.c`.

The input is a whole workspace as JSON: `{"files": [{"path", "text"}, …]}`,
with `tolean.json` among the files. The output lists each unit's result:
`{"units": [{"output", "lean"} or {"sources", "error"}, …]}`, or
`{"error"}` when the workspace has no valid `tolean.json`. One unit's error
does not hide the others. Nothing here does IO, so the page needs no file
system.
-/
namespace tolean.Web

open Lean (Json)
open tolean.Project

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

@[export tolean_web_translate]
def translateJson (input : String) : String :=
  match translateWorkspace input with
  | .ok j => j.compress
  | .error e => (Json.mkObj [("error", e)]).compress

end tolean.Web
