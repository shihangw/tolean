// certify: required

export function sum(limit: number): number {
  let total = 0;
  for (let i = 0; i < limit; i++) total += i;
  return total;
}

export function length(xs: ReadonlyArray<bigint>): number {
  let total = 0;
  for (let i = 0; i < xs.length; i++) total += 1;
  return total;
}

export function literal(): number {
  let total = 0;
  for (let i = 2; i < 7; i++) total += i;
  return total;
}

export function nearSafe(limit: number): number {
  let total = 0;
  for (let i = 9007199254740990; i < limit; i++) total += 1;
  return total;
}
