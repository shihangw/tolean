/** Source names that are also Lean names: the output writes Lean's from the root. */
export interface List {
  readonly some: bigint;
  readonly none: boolean;
}

export function decide(x: bigint | null, flag: boolean): bigint {
  if (x === null) {
    return 0n;
  }
  const Option: bigint = x * 2n;
  return flag && x > 0n ? Option : x;
}

export function pick(items: ReadonlyArray<List>, N: number): bigint {
  let total = 0n;
  for (const String of items) {
    if (String.none === Number.isNaN(N)) {
      total += String.some;
    }
  }
  return total;
}
