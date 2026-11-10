// expect: 3:3 set, add and delete are allowed only on an owned map or set
export function f(s: Set<string>): bigint {
  s.add('a');
  return 0n;
}
