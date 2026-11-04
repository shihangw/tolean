// `??` on nullable fields below the first level, which the certificate must
// split too.
interface Inner {
  readonly x: bigint | null;
}

interface Outer {
  readonly inner: Inner;
}

export function nested(p: Outer): bigint {
  return p.inner.x ?? 1n;
}

export function maybeInner(p: Inner | null): bigint {
  if (p === null) return 0n;
  return p.x ?? 2n;
}

export function total(ps: ReadonlyArray<Outer>): bigint {
  let n = 0n;
  for (const p of ps) {
    n += p.inner.x ?? 0n;
  }
  return n;
}
