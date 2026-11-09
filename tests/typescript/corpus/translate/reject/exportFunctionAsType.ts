// expect: 3:15 this file declares no interface or type named 'f' before this export list
function f(n: bigint): bigint { return n; }
export { type f };
