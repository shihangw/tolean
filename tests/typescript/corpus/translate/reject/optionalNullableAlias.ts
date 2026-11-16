type U<T> = T | undefined;
type N<T> = T | null;
// expect: 4:13 a type may not include both null and undefined
type Both = U<N<bigint>>;
export function f(v: Both): bigint | undefined { return v ?? 5n; }
