// A pattern on the rows of a table: each name is optional, `undefined` past
// the end of the row, and the rest is a new array of the values after the
// places. The certifier does not cover a loop over arrays of arrays yet, so
// this file gets no certificate.
export function heads(rows: ReadonlyArray<ReadonlyArray<bigint>>): bigint {
  let sum = 0n;
  for (const [first, ...rest] of rows) {
    if (rest.length > 0) {
      sum += first ?? 0n;
    }
  }
  return sum;
}
