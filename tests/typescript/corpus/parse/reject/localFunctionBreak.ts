// expect: 5:7 outside a loop
export function f(xs: ReadonlyArray<bigint>): void {
  for (const x of xs) {
    function g(): void {
      break;
    }
  }
}
