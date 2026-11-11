// `**` with a literal exponent, and the bitwise operators on bigints.
export function square(x: bigint): bigint { return x ** 2n; }

export function cube(x: bigint): bigint { return x ** (3n); }

export function one(x: bigint): bigint { return x ** 0n; }

export function mask(flags: bigint, bits: bigint): bigint { return flags & bits; }

export function join(a: bigint, b: bigint): bigint { return a | b; }

export function toggle(a: bigint, b: bigint): bigint { return a ^ b; }

export function complement(a: bigint): bigint { return ~a; }

export function shifted(a: bigint, n: bigint): bigint { return (a << n) + (a >> n); }

export function lowBits(a: bigint, n: bigint): bigint { return a & ((1n << n) - 1n); }

export function isSet(flags: bigint, bit: bigint): boolean { return (flags >> bit & 1n) === 1n; }
