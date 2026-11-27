// A throw out of a map borrow ends every caller with the same error.
function check(x: bigint): bigint {
  if (x < 0n) {
    throw new Error("negative");
  }
  return x;
}
function put(m: Map<bigint, bigint>, x: bigint): void {
  m.set(1n, x);
  check(x);
  m.set(2n, x);
}
function forward(m: Map<bigint, bigint>, x: bigint): void {
  put(m, x);
  m.delete(1n);
}
export function f(x: bigint): bigint {
  const m = new Map<bigint, bigint>();
  forward(m, x);
  return m.get(2n) ?? 0n;
}
