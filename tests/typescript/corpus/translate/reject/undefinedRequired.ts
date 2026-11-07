// expect: 6:12 undefined may stand only where an optional value is expected
function f(a: bigint): bigint {
  return a;
}
export function g(): bigint {
  return f(undefined);
}
