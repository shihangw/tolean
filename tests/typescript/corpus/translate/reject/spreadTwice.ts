// expect: 4:25 'x' is set twice
export interface P { readonly x: bigint; readonly note?: string; }
export function f(p: P): P {
  return { ...p, x: 1n, x: 2n };
}
