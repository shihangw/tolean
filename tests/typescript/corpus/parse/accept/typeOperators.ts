// `as const` and `satisfies T` bind like `<`: they apply to what comes before
// them at that precedence, and an operator after them applies to the result.
export const a = [1n, 2n] as const;
export const b = { kind: 'circle', r: 1n } satisfies Shape;
export const c = x + y as const;
export const d = x === y as const;
export const e = x as const + 1;
export const f = -x satisfies bigint;
export const g = x as const as const;
export const h = x satisfies ReadonlyArray<bigint> satisfies T;
export const i = c ? x as const : y satisfies T | null;
export const j = f(x as const, y satisfies T[]);
export const k = (x as const) < y;
export const l = x satisfies T
  ;
export const n = x as
  const;
export function o(p: bigint): bigint {
  return p satisfies bigint;
}
