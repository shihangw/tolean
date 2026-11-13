// Function declarations in the blocks of a function: with and without types,
// generic, nested, in a loop, and with a `return` and a loop of their own.
export function summarize(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n;
  function add(x: bigint): void {
    total += x;
  }
  for (const x of xs) {
    function twice(y: bigint): bigint {
      return y * 2n;
    }
    add(twice(x));
  }
  return total;
}

function outer(a, b?: number) {
  function first<T>(items: ReadonlyArray<T>, fallback: T): T {
    for (const item of items) {
      return item;
    }
    return fallback;
  }
  function inner() {
    function innermost(): number {
      return 1;
    }
    return innermost();
  }
  if (a) {
    function inBranch(): void {}
  }
  while (b) {
    function inLoop(): number {
      while (true) {
        break;
      }
      return 0;
    }
    break;
  }
  return first([a], inner());
}
