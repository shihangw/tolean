// expect: 5:1 a function may change only an array, a map or a set that it makes in a const, under a name that no other variable of it has, and may hand it on only in its return value
// The check is on names: the `n` of the else branch is not a new
// collection that the function owns, so the function may not change the
// array of the other `n`. Rename one of them.
export function f(b: boolean): ReadonlyArray<bigint> {
  if (b) {
    const n: Array<bigint> = [1n];
    n.push(2n);
    return n;
  } else {
    const n: ReadonlyArray<bigint> = [5n];
    return n;
  }
}
