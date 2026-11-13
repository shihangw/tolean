// target: ES2019
// expect: 3:22 the target ES2019 does not have bigint
export function f(a: bigint): bigint { return a & a; }
