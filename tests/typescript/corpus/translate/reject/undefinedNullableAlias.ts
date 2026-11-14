type Maybe = bigint | undefined;
// expect: 3:31 a type may not include both null and undefined
export function f(x: bigint): Maybe | null { return x; }
