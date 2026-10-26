/** A half-open time window, with optional ends. */
export function inWindow(
  startMs: number,
  endMs: number | null,
  cancelledMs: number | null,
  atMs: number,
): boolean {
  return (
    cancelledMs === null &&
    atMs >= startMs &&
    (endMs === null || atMs < endMs)
  );
}

export function clampStart(startMs: number, floorMs: number | null): number {
  if (floorMs === null) {
    return startMs;
  }
  return startMs < floorMs ? floorMs : startMs;
}

export function countSafe(values: ReadonlyArray<number>): number {
  let count = 0;
  for (const v of values) {
    if (Number.isSafeInteger(v) && !Number.isNaN(v)) {
      count += 1;
    }
  }
  return count;
}
