// Optional parameters of functions, with and without a type, and a required
// one after an optional one, which tsc parses and only its checker refuses.
export function f(a: number, b?: number, c?: string | null): number {
  return a;
}

function g(x?, y: bigint) {
  return y;
}

function h(
  first: bigint,
  second ? : bigint,
) {
  return first;
}
