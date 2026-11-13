// expect: 2:1 'Object' would hide the global Object
export function Object(x: bigint): bigint { return x; }
