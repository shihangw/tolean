// `Object.is`, which tells `NaN` and `-0` apart from `===` on numbers, and
// `Number(b)` on a bigint.
export function same(a: number, b: number): boolean { return Object.is(a, b); }

export function isNegativeZero(x: number): boolean { return Object.is(x, -0); }

export function sameName(a: string, b: string): boolean { return Object.is(a, b); }

export function sameCount(a: bigint, b: bigint): boolean { return Object.is(a, b) || a > b; }

export function asNumber(b: bigint): number { return Number(b); }

export function average(total: bigint, count: number): number { return Number(total) / count; }
