// expect: 9:3 'f' would hide the function or global f in its whole block
export function f(): bigint {
  return 1n;
}

// In JS, the local f is in its dead zone at the call, which throws.
export function g(): bigint {
  const y = f();
  const f = 2n;
  return y;
}
