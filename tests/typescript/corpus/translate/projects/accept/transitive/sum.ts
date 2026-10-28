// `Inner` reaches this file only through the fields of `Outer`.
import type { Outer } from "./outer.ts";

export function sum(o: Outer): bigint {
  const xs = [o.a, o.b];
  let s = 0n;
  for (const x of xs) {
    s += x.v;
  }
  return s;
}
