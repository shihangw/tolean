// expect: 4:18 'x' does not have the field's type
export interface P { readonly x: bigint; readonly note?: string; }
export function f(p: P): P {
  return { ...p, x: 'a' };
}
