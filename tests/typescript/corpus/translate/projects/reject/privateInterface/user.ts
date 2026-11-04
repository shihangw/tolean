import type { Internal } from "./base.ts";

export function read(x: Internal): bigint {
  return x.value;
}
