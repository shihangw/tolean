// expect: 3:10 the value does not have the type that 'satisfies' names
export function f(x: bigint): bigint {
  return x satisfies boolean;
}
