export function name(kind: string, n: bigint): string {
  switch (kind) {
    case 'a':
      return 'one';
    case 'b': {
      const m = n + 1n;
      if (m > 2n) return 'big';
      return 'small';
    }
    case n > 3n ? 'c' : 'd':
    case 'e':
      return 'many';
    default:
      return 'none';
  }
}

export function loop(xs: ReadonlyArray<string>): bigint {
  let count = 0n;
  for (const x of xs) {
    switch (x) {
      case 'skip':
        continue;
      case 'stop':
        break;
      default:
        count += 1n;
    }
  }
  return count;
}

export function count(x: string): bigint {
  let n = 0n;
  switch (x) {
    case 'a':
      n = 1n;
      break;
    case 'b':
      n = 2n;
      break
    default:
      break;
  }
  return n;
}

export function empty(x: string): bigint {
  switch (x) {
  }
  switch ((x)) {
    default:
  }
  return 0n;
}
