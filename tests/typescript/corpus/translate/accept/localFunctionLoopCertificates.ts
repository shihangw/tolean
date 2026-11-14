// A loop can call a lifted function, and a lifted function can contain a loop.
function doubleValue(x: bigint): bigint {
  return x * 2n;
}

export function localLoopSum(xs: ReadonlyArray<bigint>, fee: bigint): bigint {
  function sum(ys: ReadonlyArray<bigint>): bigint {
    let total = 0n;
    for (const y of ys) {
      total += doubleValue(y) - fee;
    }
    return total;
  }
  return sum(xs);
}

export function localLoopUpdate(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n;
  function add(x: bigint): void {
    total += doubleValue(x);
  }
  for (const x of xs) {
    if (x < 0n) continue;
    if (x > 100n) break;
    add(x);
  }
  return total;
}

export function localLoopNested(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n;
  function addRow(y: bigint): void {
    for (const z of xs) {
      total += y * z;
    }
  }
  for (const x of xs) {
    addRow(x);
  }
  return total;
}
