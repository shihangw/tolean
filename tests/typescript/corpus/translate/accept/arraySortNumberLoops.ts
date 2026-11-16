// certify: required
interface Row {
  readonly values: ReadonlyArray<number>;
}
export function collected(rows: ReadonlyArray<Row>): ReadonlyArray<number> {
  let result: ReadonlyArray<number> = [];
  for (const row of rows) {
    result = [...result, ...row.values.toSorted((a, b) => a - b)];
  }
  return result;
}
export function lastArray(rows: ReadonlyArray<ReadonlyArray<number>>): ReadonlyArray<number> {
  let result: ReadonlyArray<number> = [];
  for (const row of rows) {
    result = [...result, ...row.toSorted((a, b) => b - a)];
  }
  return result;
}
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function called(rows: ReadonlyArray<Row>): ReadonlyArray<number> {
  let result: ReadonlyArray<number> = [];
  for (const row of rows) {
    result = [...result, ...sorted([...row.values, 0])];
  }
  return result;
}
export function stopped(rows: ReadonlyArray<Row>): ReadonlyArray<number> {
  let result: ReadonlyArray<number> = [];
  for (const row of rows) {
    result = [...result, ...row.values.toSorted((a, b) => a - b)];
    if (row.values.length > 0) { break; }
  }
  return result;
}
export function early(rows: ReadonlyArray<Row>): ReadonlyArray<number> {
  for (const row of rows) {
    if (row.values.length > 0) {
      return row.values.toSorted((a, b) => a - b);
    }
  }
  return [];
}
export function captured(rows: ReadonlyArray<Row>, xs: ReadonlyArray<number>): ReadonlyArray<number> {
  let result: ReadonlyArray<number> = [];
  for (const row of rows) {
    result = [...result, ...xs.toSorted((a, b) => a - b), ...row.values];
  }
  return result;
}
export function nested(groups: ReadonlyArray<ReadonlyArray<Row>>): ReadonlyArray<number> {
  let result: ReadonlyArray<number> = [];
  for (const group of groups) {
    for (const row of group) {
      result = [...result, ...row.values.toSorted((a, b) => a - b)];
    }
  }
  return result;
}
