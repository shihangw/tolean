// expect: 3:10 'f' is exported already
export function f(n: bigint): bigint { return n; }
export { f };
