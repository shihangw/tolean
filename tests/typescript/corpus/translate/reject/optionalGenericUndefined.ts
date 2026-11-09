// expect: 6:52 undefined may stand only where an optional value is expected
function take<T>(x?: T): T | null {
  if (x === undefined) return null;
  return x;
}
export function use(): bigint | null { return take(undefined); }
