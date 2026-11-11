// expect: 4:19 a spread '...' may only come first in an object literal
export interface P { readonly x: bigint; readonly note?: string; }
export function f(p: P): P {
  return { x: 1n, ...p };
}
