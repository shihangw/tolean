// `findIndex` is the position of the first element that passes, as a
// number, or -1. `findLast` looks from the end.
export interface Task {
  readonly id: bigint;
  readonly done: boolean;
}

export function firstNegative(xs: ReadonlyArray<bigint>): number {
  return xs.findIndex((x) => x < 0n);
}

export function hasNegative(xs: ReadonlyArray<bigint>): boolean {
  return xs.findIndex((x) => x < 0n) !== -1;
}

export function indexOfName(names: ReadonlyArray<string>, name: string): number {
  return names.findIndex((n) => n === name);
}

export function lastDone(tasks: ReadonlyArray<Task>): bigint {
  return tasks.findLast((t) => t.done)?.id ?? -1n;
}

export function lastBig(xs: ReadonlyArray<number>, limit: number): number {
  return xs.findLast((x) => x > limit) ?? 0;
}

export function firstDoneIndexes(rows: ReadonlyArray<ReadonlyArray<boolean>>): ReadonlyArray<number> {
  return rows.map((r) => r.findIndex((b) => b));
}
