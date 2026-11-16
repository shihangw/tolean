type U<T> = T | undefined;
type N<T, V> = [T | null, V];
// expect: 4:13 a type may not include both null and undefined
type Both = N<U<bigint>, boolean>;
export function f(v: Both): bigint | undefined { return v[0] ?? 5n; }
