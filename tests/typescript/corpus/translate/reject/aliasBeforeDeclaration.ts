// expect: 2:22 unsupported type
export function f(x: Id): bigint { return x; }
type Id = bigint;
