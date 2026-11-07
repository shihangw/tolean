import { clamp, next, type Range } from "./lib.ts";

export function middle(r: Range): bigint {
  return clamp(next(r.lo, r), r);
}
