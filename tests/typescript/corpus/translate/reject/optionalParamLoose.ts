// expect: 3:12 undefined may stand only where an optional value is expected
export function f(a?: bigint): boolean {
  if (a == undefined) {
    return true;
  }
  return false;
}
