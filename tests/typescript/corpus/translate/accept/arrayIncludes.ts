// `xs.includes(x)` becomes `x ∈ xs` on bigints, booleans, strings and
// literal unions. On numbers it becomes `List.any` with
// `JSNumber.sameValueZero`, which finds `NaN` as JS does.
export type Color = 'red' | 'green' | 'blue';

export function hasZero(xs: ReadonlyArray<bigint>): boolean {
  return xs.includes(0n);
}

export function hasName(names: ReadonlyArray<string>, name: string): boolean {
  return names.includes(name);
}

export function anyTrue(flags: ReadonlyArray<boolean>): boolean {
  return flags.includes(true);
}

export function hasRed(colors: ReadonlyArray<Color>): boolean {
  return colors.includes('red');
}

export function hasNaN(xs: ReadonlyArray<number>): boolean {
  return xs.includes(NaN);
}

export function hasEither(xs: ReadonlyArray<number>, a: number, b: number): boolean {
  return xs.includes(a) || xs.includes(b);
}

export function missing(xs: ReadonlyArray<bigint>, x: bigint): boolean {
  return !xs.includes(x);
}

export function known(xs: ReadonlyArray<bigint>, ids: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.filter((x) => ids.includes(x));
}

export function countKnown(xs: ReadonlyArray<string>, ids: ReadonlyArray<string>): bigint {
  let n = 0n;
  for (const x of xs) {
    if (ids.includes(x)) {
      n = n + 1n;
    }
  }
  return n;
}

export function inLiteral(c: Color): boolean {
  const warm: ReadonlyArray<Color> = ['red'];
  return warm.includes(c);
}
