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

// Source separators need not match the printer's canonical semicolons.
export type Commas = { readonly a: bigint, readonly b: bigint, };
export type Newlines = {
  readonly a: bigint
  readonly b: { readonly c: bigint }
};
export type Mixed = {
  readonly a: { readonly b: bigint, readonly c: bigint };
  readonly xs: ReadonlyArray<{ readonly n: bigint }>
  readonly pair: [{ readonly n: bigint }, { readonly n: bigint }],
};

export function id(x: { readonly n: bigint }): { readonly n: bigint } {
  return x;
}

export const checked = { n: 1n } satisfies { readonly n: bigint };
export const nestedChecked = ({ n: 1n } satisfies { readonly n: bigint }).n;
