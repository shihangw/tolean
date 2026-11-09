// expect: 3:10 === here would compare objects
export function f(a: [bigint, bigint], b: [bigint, bigint]): boolean {
  return a === b;
}
