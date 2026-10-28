import type { Inner } from "./inner.ts";

export interface Outer {
  readonly a: Inner;
  readonly b: Inner;
}
