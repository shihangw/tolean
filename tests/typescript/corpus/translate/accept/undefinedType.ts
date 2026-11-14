export function empty(): bigint | undefined {
  return undefined;
}

export function present(x: bigint): undefined | bigint {
  return x;
}

export function localValue(x: bigint): bigint {
  let value: bigint | undefined = undefined;
  value = x;
  return value ?? 0n;
}

export function read(x?: bigint): bigint | undefined {
  const value: bigint | undefined = x;
  return value;
}
