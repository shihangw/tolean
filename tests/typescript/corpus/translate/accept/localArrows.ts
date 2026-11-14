// Arrow functions with a body in braces, stored in a `const`. Each is a
// local function, so the output lifts it out as it lifts a declaration.
export function tally(xs: ReadonlyArray<bigint>, limit: bigint): bigint {
  let over = 0n;
  let under = 0n;
  const count = (x: bigint): void => {
    if (x > limit) {
      over += 1n;
    } else {
      under += 1n;
    }
  };
  const weight = (x: bigint): bigint => {
    return x * 2n + limit;
  };
  for (const x of xs) {
    count(x);
  }
  const w = weight(over);
  return w - under;
}
