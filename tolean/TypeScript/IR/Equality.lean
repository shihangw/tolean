import tolean.IR.Equality
import tolean.TypeScript.IR

/-!
Equality on the Tolean IR with the TypeScript extension, as a function that
the kernel can run. The shared IR proves it in `tolean/IR/Equality.lean`, for
every extension whose types and operations derive `DecidableEq`, as those of
`tolean/TypeScript/IR.lean` do.
-/
