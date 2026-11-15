export function positive(x?: bigint): boolean {
  return x !== undefined && x > 0n;
}

export function absentOrPositive(x?: bigint): boolean {
  return undefined === x || x > 0n;
}

export function negated(x?: bigint): boolean {
  return !(x === undefined) && x > 0n;
}

export function negatedOr(x?: bigint): boolean {
  return !(undefined !== x) || x > 0n;
}

export function choice(x?: bigint): bigint {
  return x === undefined ? 0n : x + 1n;
}

export function reversedChoice(x?: bigint): bigint {
  return x !== undefined ? x + 1n : 0n;
}

export function negatedChoice(x?: bigint): bigint {
  return !(x === undefined) ? x + 1n : 0n;
}

export function optionalChoice(x?: bigint): bigint | undefined {
  return x === undefined ? undefined : x + 1n;
}
