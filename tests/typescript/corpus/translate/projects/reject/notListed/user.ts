import { hidden } from "./lib.ts";

export function f(x: bigint): bigint {
  return hidden(x);
}
