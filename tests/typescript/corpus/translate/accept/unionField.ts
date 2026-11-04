// A tagged union in a field of an interface, and in a member of another
// union, which the certificate's codecs must declare in order.
interface A {
  readonly kind: 'a';
  readonly n: bigint;
}

interface B {
  readonly kind: 'b';
  readonly n: bigint;
}

type U = A | B;

interface Box {
  readonly value: U;
}

export function inBox(b: Box): bigint {
  const u = b.value;
  if (u.kind === 'a') return u.n;
  return u.n;
}

interface Wrapped {
  readonly tag: 'wrapped';
  readonly inner: U;
}

interface Plain {
  readonly tag: 'plain';
  readonly n: bigint;
}

type V = Wrapped | Plain;

export function depth(v: V): bigint {
  if (v.tag === 'plain') return v.n;
  const u = v.inner;
  if (u.kind === 'a') return u.n + 1n;
  return u.n + 2n;
}
