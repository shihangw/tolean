// A tuple satisfies a tuple type when each element has the element type
// there. The value keeps its own type.
type U = string | bigint;

export function keep(p: [string, bigint]): [string, bigint] {
  return p satisfies [U, bigint];
}

export function nested(p: [string, [bigint, string]]): [string, [bigint, string]] {
  return p satisfies [U, [U, string]];
}
