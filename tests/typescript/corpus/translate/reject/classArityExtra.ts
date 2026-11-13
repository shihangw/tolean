// expect: 9:21 'TooMany' takes 2 arguments
// One argument more than the constructor takes: JS would bind limit to "oops" and drop "x".
export class TooMany extends Error {
  constructor(readonly limit: bigint, extra: string) {
    super("too many: " + extra);
  }
}
export function f(n: bigint): bigint {
  if (n > 9n) throw new TooMany("oops", n, "x");
  return n;
}
