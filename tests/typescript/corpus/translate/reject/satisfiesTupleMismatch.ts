// expect: 4:10 the value does not have the type that 'satisfies' names
type U = string | bigint;
export function keep(p: [string, bigint]): [string, bigint] {
  return p satisfies [U, string];
}
