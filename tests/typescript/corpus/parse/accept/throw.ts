// `throw` takes any expression on the same line, and ends at a `;` or where
// one is inserted.
export function check(n: bigint): bigint {
  if (n < 0n) throw "negative";
  if (n > 9n) {
    throw { code: 1, message: "too big" };
  }
  throw n
}

export function nested(xs: bigint[]): bigint {
  for (const x of xs) {
    switch (x) {
      case 1n:
        throw x + 1n;
      default:
        break;
    }
  }
  throw (xs);
}
