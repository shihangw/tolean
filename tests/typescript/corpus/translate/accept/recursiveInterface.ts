export interface Node {
  readonly value: bigint;
  readonly next: Node | null;
}

export function pair(a: bigint, b: bigint): Node {
  const tail: Node = { value: b, next: null };
  return { value: a, next: tail };
}

export function second(n: Node): bigint | null {
  const next = n.next;
  if (next === null) return null;
  return next.value;
}

export interface Tree<T> {
  readonly value: T;
  readonly children: ReadonlyArray<Tree<T>>;
}

export function leaf<T>(value: T): Tree<T> {
  return { value: value, children: [] };
}

export function childValues(t: Tree<bigint>): ReadonlyArray<bigint> {
  return t.children.map(c => c.value);
}

interface Folder {
  readonly name: string;
  readonly parent?: Folder;
  readonly entries: ReadonlyArray<[string, Folder | null]>;
}

export function parentName(f: Folder): string {
  return f.parent?.name ?? '';
}
