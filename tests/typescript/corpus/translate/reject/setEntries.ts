// expect: 3:10 new Set takes no elements here
export function f(): Set<string> {
  return new Set<string>(['a']);
}
