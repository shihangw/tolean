function values(absent: boolean): bigint[] | null {
  return absent ? null : [1n];
}

export function f(): bigint {
  return values(Number.isNaN(NaN))?.[0] ?? 0n;
}
