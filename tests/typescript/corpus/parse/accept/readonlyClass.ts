class Empty {}

export class Counter {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  plus(x: bigint): bigint { return this.value + x; }
  twice(): bigint { return this.plus(this.value); }
}

class ParamField {
  readonly other: bigint;
  constructor(readonly value: bigint) { this.other = value + 1n; }
  get(): bigint { return this.value; }
}
