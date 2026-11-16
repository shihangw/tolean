// certify: required
export function identity(x: { readonly n: bigint }): { readonly n: bigint } {
  return x;
}

export function made(n: bigint): { readonly n: bigint } {
  return { n };
}

export type Box = {
  readonly inner: { readonly n: bigint };
  readonly extra?: bigint | null;
};

export function copy(box: Box): Box {
  return box;
}

export function build(n: bigint): Box {
  return { inner: { n } };
}

export function total(box: Box): bigint {
  return box.inner.n + (box.extra ?? 0n);
}

export function empty(): {} {
  return {};
}
