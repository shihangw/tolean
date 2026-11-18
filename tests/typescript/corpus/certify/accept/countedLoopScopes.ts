// certify: required

export interface Limit {
  value: number;
}

export function nullable(limit: number | null): number {
  if (limit === null) return 0;
  let total = 0;
  for (let i = 0; i < limit; i++) total += i;
  return total;
}

export function optional(limit?: number): number {
  if (limit === undefined) return 0;
  let total = 0;
  for (let i = 0; i < limit; i++) total += i;
  return total;
}

export function nullableRecord(limit: Limit | null): number {
  if (limit === null) return 0;
  let total = 0;
  for (let i = 0; i < limit.value; i++) total += i;
  return total;
}

export function inForOf(xs: ReadonlyArray<bigint>, limit: number): number {
  let total = 0;
  for (const x of xs) {
    for (let i = 9007199254740990; i < limit; i++) total += 1;
  }
  return total;
}

export function inCounted(outer: number, limit: number): number {
  let total = 0;
  for (let j = 0; j < outer; j++) {
    for (let i = 9007199254740990; i < limit; i++) total += 1;
  }
  return total;
}

export function deeper(xs: ReadonlyArray<bigint>, outer: number, limit: number): number {
  let total = 0;
  for (const x of xs) {
    for (let j = 0; j < outer; j++) {
      for (let i = 9007199254740990; i < limit; i++) total += 1;
    }
  }
  return total;
}

export function narrowedNested(xs: ReadonlyArray<bigint>, limit: number | null): number {
  if (limit === null) return 0;
  let total = 0;
  for (const x of xs) {
    for (let i = 0; i < limit; i++) total += i;
  }
  return total;
}

export function narrowedInLoop(xs: ReadonlyArray<bigint>, limit: Limit | null): number {
  let total = 0;
  for (const x of xs) {
    if (limit !== null) {
      for (let i = 0; i < limit.value; i++) total += i;
    }
  }
  return total;
}
