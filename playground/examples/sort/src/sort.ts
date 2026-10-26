/** Insert x into the sorted array xs, before the first larger element. */
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

/** An empty array. Tolean's subset does not yet accept `let out: ReadonlyArray<bigint> = []`. */
function empty(): ReadonlyArray<bigint> {
  const out: Array<bigint> = [];
  return out;
}

/** The elements of xs in ascending order. */
export function sort(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  let out = empty();
  for (const x of xs) {
    out = insert(out, x);
  }
  return out;
}
