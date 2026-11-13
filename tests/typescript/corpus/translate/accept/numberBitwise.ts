// The bitwise operators on numbers, which work on 32-bit integers.
export function toInt32(x: number): number { return x | 0; }

export function toUint32(x: number): number { return x >>> 0; }

export function flags(a: number, b: number): number { return (a & b) ^ (a | b); }

export function complement(x: number): number { return ~x; }

export function shifted(x: number, n: number): number { return (x << n) + (x >> n); }

export function isOdd(x: number): boolean { return (x & 1) === 1; }
