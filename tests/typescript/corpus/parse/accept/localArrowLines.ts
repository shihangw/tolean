// A line break inside the parameters or the return type of a local arrow
// function is fine; only one right before `=>` is not (ECMA-262 §15.3).
export function f(xs: ReadonlyArray<bigint>): bigint {
  let n = 0n;
  const add = (x: bigint
  ): void => {
    n += x;
  };
  const twice = (x: bigint): Array<
    bigint> => {
    return [x, x];
  };
  for (const x of xs) {
    add(x);
  }
  return n + BigInt(twice(n).length);
}
