export function f(): bigint {
  const m = new Map<string, bigint>();
  const s = new Set<ReadonlyArray<bigint>>();
  const e = new Error("bad", m);
  const n = new Thing().size;
  const c = new Box<readonly [bigint, string]>(1n)(2n);
  const g = (a: bigint) => new Pair<bigint, Array<bigint | null>>(a, [a]);
  return new Counter(new Map<bigint, bigint>()).total;
}
export function g(): void {
  new Audit("start").log();
}
