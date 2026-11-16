type U<T, V> = [T | undefined, V];
type N<T> = T | null;
// expect: 4:13 a type may not include both null and undefined
type Both = U<N<bigint>, boolean>;
export function f(v: Both): bigint | undefined { return v[0] ?? 5n; }
