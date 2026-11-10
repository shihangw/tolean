export interface Node {
  readonly value: bigint;
  readonly next: Node | null;
}

export function length(n: Node): bigint {
  const next = n.next;
  if (next === null) return 1n;
  return 1n + length(next);
}

export function sumFrom(n: Node | null): bigint {
  if (n === null) return 0n;
  return n.value + sumFrom(n.next);
}

export function nth(k: bigint, n: Node): bigint {
  if (k <= 0n) return n.value;
  const next = n.next;
  if (next === null) return n.value;
  return nth(k - 1n, next);
}

export interface Tree<T> {
  readonly value: T;
  readonly children: ReadonlyArray<Tree<T>>;
}

export function size<T>(t: Tree<T>): bigint {
  let total = 1n;
  for (const c of t.children) {
    total += size(c);
  }
  return total;
}

export function sizes(t: Tree<bigint>): ReadonlyArray<bigint> {
  return t.children.map(c => size(c));
}

export function allPositive(t: Tree<bigint>): boolean {
  return t.value > 0n && t.children.every(c => allPositive(c));
}

export function hasLarge(t: Tree<bigint>, limit: bigint): boolean {
  return t.children.find(c => c.value > limit || hasLarge(c, limit)) !== undefined;
}

export function firstLarge(t: Tree<bigint>, limit: bigint): bigint {
  if (t.value > limit) return t.value;
  let found = 0n;
  for (const c of t.children) {
    const v = firstLarge(c, limit);
    if (v > limit) {
      found = v;
      break;
    }
  }
  return found;
}

interface Folder {
  readonly name: string;
  readonly parent?: Folder;
  readonly entries: ReadonlyArray<[string, Folder | null]>;
}

export function files(f: Folder): bigint {
  let n = 0n;
  for (const e of f.entries) {
    const sub = e[1];
    if (sub === null) {
      n += 1n;
    } else {
      n += files(sub);
    }
  }
  return n;
}

export function depth(f: Folder): bigint {
  const p = f.parent;
  if (p === undefined) return 0n;
  return 1n + depth(p);
}
