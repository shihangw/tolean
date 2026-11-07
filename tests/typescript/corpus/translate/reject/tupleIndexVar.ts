// expect: 3:12 the index of a tuple must be a number literal
export function f(t: [bigint, bigint], i: number): bigint {
  return t[i];
}
