// A callback reads the locals in scope at the call: parameters, `let` locals,
// a loop's element and state, and the parameter of an outer callback. Its body
// may call a function of the file.
export interface Order {
  readonly id: bigint;
  readonly tags: ReadonlyArray<bigint>;
}

function double(x: bigint): bigint {
  return x * 2n;
}

export function doubled(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.map(x => double(x));
}

export function shared(xs: ReadonlyArray<bigint>, ys: ReadonlyArray<bigint>): boolean {
  return xs.some(x => ys.some(y => x === y));
}

export function tagged(orders: ReadonlyArray<Order>, tag: bigint): ReadonlyArray<bigint> {
  return orders.filter(o => o.tags.some(t => t === tag)).map(o => o.id);
}

export function countAbove(orders: ReadonlyArray<Order>, limit: bigint): bigint {
  let count = 0n;
  for (const o of orders) {
    if (o.tags.every(t => t > limit + count)) {
      count += 1n;
    }
  }
  return count;
}

export function shifted(xs: ReadonlyArray<bigint>, delta: bigint): ReadonlyArray<bigint> {
  let step = delta;
  step += 1n;
  return xs.map(x => x + step);
}

export function literal(k: bigint): ReadonlyArray<bigint> {
  return [1n, 2n, 3n].map(x => x * k);
}

export function missing(xs: ReadonlyArray<bigint>): boolean {
  return xs.find(x => x === 0n) === undefined;
}
