/-!
The Tolean release. Generated files name it, so that the drift check sees an
upgrade. It must equal `version` in `npm/package.json`;
`tests/typescript/checkTranslate.ts` fails when the two differ.
-/
namespace tolean

def version : String := "0.1.0"

end tolean
