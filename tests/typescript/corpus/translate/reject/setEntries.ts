// expect: 3:26 the elements do not have the element type of the set
export function f(): Set<string> {
  return new Set<string>(new Map<string, bigint>());
}
