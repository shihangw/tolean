import type { Public } from "./base.ts";

export function read(x: Public): bigint {
  return x.value + x.deep.d;
}

export function make(v: bigint): Public {
  return { value: v, deep: { d: 0n } };
}
