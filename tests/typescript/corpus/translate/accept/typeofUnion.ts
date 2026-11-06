export type Id = string | bigint;

export function next(id: Id): bigint {
  if (typeof id === 'string') {
    return 0n;
  }
  return id + 1n;
}

export function pick(named: boolean, n: bigint): Id {
  if (named) return 'first';
  return n;
}

export function rename(id: Id, name: string): Id {
  let out: Id = id;
  if ('bigint' === typeof id) {
    out = name;
  }
  return out;
}

export function maybeNext(id: Id | null): bigint {
  if (id === null) return 0n;
  return next(id);
}

export function count(n: bigint): bigint {
  return next(n);
}

export function choose(flag: boolean): Id {
  return flag ? 'a' : 5n;
}

export function orDefault(id: Id | null): Id {
  return id ?? 'none';
}

interface Box {
  readonly id: Id;
}

export function box(n: bigint): Box {
  return { id: n };
}

export function unbox(b: Box): bigint {
  const id = b.id;
  if (typeof id === 'string') return 1n;
  return id;
}

type Cell = number | string | boolean;

export function weight(c: Cell): number {
  if (typeof c === 'number') return c;
  if (typeof c !== 'boolean') return 0;
  return c ? 1 : 0;
}

export function total(cells: ReadonlyArray<Cell>): number {
  let sum = 0;
  for (const c of cells) {
    if (typeof c === 'number') {
      sum += c;
    } else {
      sum += weight(c);
    }
  }
  return sum;
}

export function cells(flag: boolean, n: number): ReadonlyArray<Cell> {
  return [flag, n, 'x'];
}
