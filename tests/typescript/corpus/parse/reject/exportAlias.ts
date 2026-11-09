// expect: 3:12 no 'as'
function f(n: bigint): bigint { return n; }
export { f as g };
