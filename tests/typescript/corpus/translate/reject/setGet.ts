// expect: 3:10 a set has no get; use has
export function f(s: ReadonlySet<string>): bigint {
  return s.get('a') ?? 0n;
}
