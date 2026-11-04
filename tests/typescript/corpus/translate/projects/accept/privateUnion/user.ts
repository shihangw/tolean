import type { Public } from "./base.ts";

export function isHigh(x: Public): boolean {
  return x.level === 'high';
}

export function low(): Public {
  return { level: 'low' };
}
