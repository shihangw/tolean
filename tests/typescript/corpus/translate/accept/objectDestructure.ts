// certify: required
export interface Pair {
  readonly a: number;
  readonly b: number;
  readonly extra: number;
}

export function getPair(o: Pair): Pair { return o; }

export function swap(o: Pair): number {
  const { a: b, b: a } = o;
  return a - b;
}

export function partialFields(o: Pair): number {
  const { b: x } = o;
  return x;
}

export function repeated(o: Pair): number {
  const { a: x, a: y } = o;
  return x + y;
}

export function fromCall(o: Pair): number {
  const { a, b } = getPair(o);
  return a - b;
}

export function literal(): number {
  const { a, b }: Pair = { a: 1, b: 2, extra: 3 };
  return a + b;
}

export function update(o: Pair): number {
  let { a: x, b } = o;
  x = x + b;
  return x;
}

export function collision(o: Pair): number {
  const _objectField0 = 7;
  const { a, b } = o;
  return a + b + _objectField0;
}
