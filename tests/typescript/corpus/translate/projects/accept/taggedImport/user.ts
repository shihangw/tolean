import type { Shape } from "./base.ts";

export function size(s: Shape): bigint {
  if (s.kind === 'circle') return s.r;
  return s.side;
}

export function dot(): Shape {
  return { kind: 'circle', r: 0n };
}
