// expect: 4:25 JSON.stringify needs a string, a number, a boolean or null
// JSON.stringify throws a TypeError on a bigint, even inside an array.
export function render(xs: ReadonlyArray<bigint>): string {
  return JSON.stringify(xs);
}
