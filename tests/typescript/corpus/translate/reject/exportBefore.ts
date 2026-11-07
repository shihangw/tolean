// expect: 2:10 this file declares no function named 'f' before this export list
export { f };
function f(n: bigint): bigint { return n; }
