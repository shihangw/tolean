// certify: required
interface Row {
  readonly key: number;
  readonly values: ReadonlyArray<number>;
}
export function nestedSome(xs: ReadonlyArray<Row>): Row[] {
  return xs.filter(x => x.values.some(y => y > 0)).toSorted((a, b) => a.key - b.key);
}
export function nestedEvery(xs: ReadonlyArray<Row>): Row[] {
  return xs.filter(x => x.values.every(y => y > 0) && x.values.some(z => z < 10))
    .toSorted((a, b) => (a.key < b.key) ? -1 : (a.key > b.key) ? 1 : 0);
}
