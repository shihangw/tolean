// An array literal is a value: in JS it makes a new array, and nothing may
// push to an array that the function does not own.
export function insert(xs: ReadonlyArray<bigint>, x: bigint): ReadonlyArray<bigint> {
  const out: Array<bigint> = [];
  let placed = false;
  for (const y of xs) {
    if (!placed && x <= y) {
      out.push(x);
      placed = true;
    }
    out.push(y);
  }
  if (!placed) {
    out.push(x);
  }
  return out;
}

export function sort(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  let out: ReadonlyArray<bigint> = [];
  for (const x of xs) {
    out = insert(out, x);
  }
  return out;
}
