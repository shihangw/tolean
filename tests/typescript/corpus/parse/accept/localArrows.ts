// Arrow functions with a body in braces, stored in a `const` in a function:
// with and without a return type, without parameters, with a `;` and
// without one, nested, and with a loop of their own. An arrow function whose
// body is an expression stays the value of a declaration.
export function summarize(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n;
  const add = (x: bigint): void => {
    total += x;
  };
  const twice = (y: bigint) => {
    return y * 2n;
  }
  const none = (): number => {
    const inner = (): number => {
      for (const x of xs) {
        if (x > 0n) break;
      }
      return 1;
    };
    return inner();
  };
  const square = (z: bigint) => z * z;
  for (const x of xs) {
    add(twice(square(x)));
  }
  return total + BigInt(none());
}
