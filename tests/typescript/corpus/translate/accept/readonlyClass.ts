// certify: required
export class Counter {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  plus(x: bigint): bigint { return this.value + x; }
}

export function add(x: bigint, y: bigint): bigint {
  const c = new Counter(x);
  return c.plus(y);
}
