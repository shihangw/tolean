// A function of another file throws the errors of its file, which this one
// cannot pass on while either declares error classes.
import { checked } from "./lib.ts";

export function twice(n: bigint): bigint {
  const k = checked(n);
  return k * 2n;
}
