// `/` on numbers, the functions of `Math` whose results ECMA-262 defines
// exactly, and `Number.isInteger`.
export function half(x: number): number { return Math.floor(x / 2); }

export function ratio(a: number, b: number): number { return a / b; }

export function clamp(x: number, lo: number, hi: number): number {
  return Math.min(Math.max(x, lo), hi);
}

export function range(a: number, b: number, c: number): number {
  return Math.max(a, b, c) - Math.min(a, b, c);
}

export function noArguments(): number { return Math.min() - Math.max(); }

export function oneArgument(x: number): number { return Math.max(x); }

export function rounded(x: number): number {
  return Math.round(x) + Math.ceil(x) + Math.trunc(x) + Math.abs(x);
}

export function whole(x: number): boolean { return Number.isInteger(x) && x / 3 > 1; }
