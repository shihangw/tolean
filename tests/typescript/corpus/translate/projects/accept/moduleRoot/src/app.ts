// The Lean package's modules start at src/, so this imports «my-lib».Util.
import { inc } from "./my-lib/util.ts";

export function twice(x: bigint): bigint {
  return inc(inc(x));
}
