// expect: 2:48 '~' needs a bigint
export function f(a: boolean): bigint { return ~a; }
