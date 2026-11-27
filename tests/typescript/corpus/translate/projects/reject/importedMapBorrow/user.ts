import { put } from "./lib.ts";

export function f(k: string): bigint {
  const m = new Map<string, bigint>();
  put(m, k);
  return m.get(k) ?? 0n;
}
