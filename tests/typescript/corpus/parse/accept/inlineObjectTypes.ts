export type Range = { readonly lo: bigint; hi?: bigint };
export type Empty = {};

export type Shape =
  | { readonly kind: 'circle'; readonly radius: number }
  | { readonly kind: 'square'; readonly side: number };

export function measure(
  box: { readonly width: number; readonly height: number },
): { readonly lo: bigint; readonly hi: bigint } {
  return { lo: 0n, hi: 1n };
}

interface Nested {
  readonly point: { readonly x: bigint; readonly y: bigint };
  readonly items: ReadonlyArray<{ readonly n: bigint }>;
}
