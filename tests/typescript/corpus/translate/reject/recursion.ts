// expect: 2:1 a function may call itself only on a part of one of its parameters, the same one in every call
export function f(x: bigint): bigint { return f(x); }
