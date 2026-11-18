class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  map(): bigint { return this.value; }
  length(): bigint { return this.value; }
}
export function literal(): bigint[] { return [1n, 2n].map(x => x + 1n); }
export function inferred(): bigint[] {
  const xs = [1n, 2n];
  return xs.map(x => x + 1n);
}
export function annotated(): bigint[] {
  const xs: bigint[] = [1n, 2n];
  return xs.map(x => x + 1n);
}
export function length(): number {
  const xs = [1n, 2n];
  return xs.length + [3n].length;
}
export function dispatched(): bigint { return new C(7n).map(); }
