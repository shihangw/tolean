// expect: 5:19 outside a loop
export function f(a: bigint): bigint {
  switch (a) {
    case 1n:
      if (a > 0n) break;
  }
  return 0n;
}
