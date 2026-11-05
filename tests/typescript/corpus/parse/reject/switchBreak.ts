// expect: 5:7 outside a loop
export function f(a: bigint): bigint {
  switch (a) {
    case 1n:
      break;
  }
  return 0n;
}
