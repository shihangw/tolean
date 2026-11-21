function take(x?: bigint): bigint {
  return x ?? 0n;
}

function generic<T>(x?: T): T | null {
  if (x === undefined) return null;
  return x;
}

function nullableGeneric<T>(x: T | null): T | null {
  return x;
}

export function positions(x: bigint): bigint {
  let value = [x][0];
  value = x ** 2n;
  value = x + 1n;
  value = x - 1n;
  value = x * 2n;
  value = -x;
  const declared: bigint | null = x ** 2n;
  const argument = take(x ** 2n);
  const inferred = generic(x ** 2n);
  const nullable = nullableGeneric(x ** 2n);
  return (value ?? 0n) + (declared ?? 0n) + argument + (inferred ?? 0n) + (nullable ?? 0n);
}

export function returned(x: bigint): bigint | null {
  return x ** 2n;
}

export function optionalDeclared(x: bigint): bigint | undefined {
  const value: bigint | undefined = x ** 2n;
  return value;
}

export function optionalReturned(x: bigint): bigint | undefined {
  return -x;
}

export function conditional(x: bigint, flag: boolean): bigint {
  const value = flag ? x ** 2n : null;
  return value ?? 0n;
}

export function narrowed(x?: bigint): bigint {
  const value = x === undefined ? x : x ** 2n;
  return value ?? 0n;
}

export function loop(x: bigint): bigint {
  let value = [x][0];
  for (const item of [x]) {
    value = item + 1n;
  }
  return value ?? 0n;
}

export function otherTypes(x: number, s: string, b: boolean): boolean {
  let numberValue = [x][0];
  let stringValue = [s][0];
  let booleanValue = [b][0];
  numberValue = -x;
  stringValue = s + "!";
  booleanValue = !b;
  for (const item of [x]) {
    numberValue = item + 1;
    stringValue = s + "?";
    booleanValue = b && true;
  }
  return (numberValue ?? 0) > 0 && (stringValue ?? "") === s && (booleanValue ?? false);
}

export function compound(x: bigint): bigint {
  let value: bigint | null = x;
  value ??= x ** 2n;
  return value ?? 0n;
}
