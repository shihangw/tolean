import tolean.Project

/-!
The entry point into the translator for the playground. `build.sh` compiles
it to WebAssembly, and the page calls it through `glue.c`. It is
`Project.workspaceJson`, which `tolean translate-workspace` runs natively.
-/
namespace tolean.Web

@[export tolean_web_translate]
def translateJson (input : String) : String := Project.workspaceJson input

end tolean.Web
