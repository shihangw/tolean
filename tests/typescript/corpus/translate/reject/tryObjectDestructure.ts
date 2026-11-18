// expect: 7:3 try bodies allow only literal values, reads, strict equality, local initializers, if, return and throw new Error; mutation, calls and other operations need exception analysis
export interface Pair {
  readonly a: bigint;
  readonly b: bigint;
}
export function inTry(pair: Pair): bigint {
  try {
    const { a, b } = pair;
    return a;
  } catch (ignored) {
    return 7n;
  }
}
