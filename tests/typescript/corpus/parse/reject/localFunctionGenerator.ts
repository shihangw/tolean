// expect: 3:11 generators are not supported
export function f(): void {
  function* g(): void {}
}
