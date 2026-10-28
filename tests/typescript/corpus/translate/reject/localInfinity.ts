// expect: 6:3 'Infinity' would hide the function or global Infinity
// In JS, the local Infinity is in its dead zone from the start of the block,
// so the read of Infinity before it throws.
export function g(): number {
  const x = Infinity;
  const Infinity = 1;
  return x;
}
