// expect: 4:10 'f' is in two export lists
function f(n: bigint): bigint { return n; }
export { f };
export { f };
