type Tag = 'urgent' | 'later';

interface Task {
  readonly owner: string;
  readonly tag: Tag;
}

/** The number of distinct owners. */
export function owners(tasks: ReadonlyArray<Task>): number {
  const seen = new Set<string>();
  for (const t of tasks) {
    seen.add(t.owner);
  }
  return seen.size;
}

export function without(xs: ReadonlyArray<bigint>, drop: bigint): Set<bigint> {
  const s: Set<bigint> = new Set();
  for (const x of xs) {
    if (x !== drop) s.add(x);
  }
  s.delete(0n);
  return s;
}

export function urgent(tags: ReadonlySet<Tag>): boolean {
  return tags.has('urgent') && !tags.has('later');
}

export function both(s: ReadonlySet<boolean>): boolean {
  return s.has(true) && s.has(false);
}
