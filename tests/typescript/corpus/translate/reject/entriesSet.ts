// expect: 4:21 a loop must run over an array, a set, a map or xs.entries()
export function f(s: ReadonlySet<bigint>): bigint {
  let total = 0n;
  for (const [x] of s.entries()) {
    total = total + x;
  }
  return total;
}
