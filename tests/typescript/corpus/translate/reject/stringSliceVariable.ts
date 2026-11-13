// expect: 4:10 'slice' on a string takes at most two integer literals
// The bounds must be integer literals, as for an array.
export function f(s: string, i: number): string {
  return s.slice(i);
}
