// The message of an error class may hold an arrow function. Each argument
// that is not a literal first moves to a hoisted name, so no binder of the
// source captures a replacement, and the substitution stops at the arrow's
// own parameters. An arrow parameter may not share a name with a parameter
// of the constructor or a local of the function: the shadow rule holds for
// the message as for any arrow.
export class Near extends Error {
  constructor(readonly n: bigint) {
    super([1n, 2n].some((k) => k === n) ? "near" : "far");
  }
}
export function g(x: bigint): bigint {
  const m = x + 1n;
  if (m > 3n) throw new Near(m);
  return m;
}
