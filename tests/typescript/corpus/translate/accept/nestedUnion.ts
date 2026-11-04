// A literal union below the first level of a parameter, which the
// certificate must split too.
type Status = 'on' | 'off';

interface Inner {
  readonly s: Status;
}

interface Outer {
  readonly inner: Inner;
}

export function isOn(x: Outer): boolean {
  return x.inner.s === 'on';
}

export function isOff(x: Inner | null): boolean {
  if (x === null) return false;
  return x.s === 'off';
}

export function countOn(xs: ReadonlyArray<Outer>): bigint {
  let n = 0n;
  for (const x of xs) {
    if (x.inner.s === 'on') {
      n += 1n;
    }
  }
  return n;
}
