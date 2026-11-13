// expect: 2:1 'Date' would hide the global Date
export function Date(x: bigint): bigint { return x; }
