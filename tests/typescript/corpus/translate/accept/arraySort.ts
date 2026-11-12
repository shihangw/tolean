// A sort with a comparator of keys: toSorted, or sort on a new array.
interface Task {
  readonly id: bigint;
  readonly name: string;
  readonly priority: bigint;
}

interface Entry {
  readonly task: Task;
  readonly note: string;
}

export function byPriority(tasks: ReadonlyArray<Task>): Task[] {
  return tasks.toSorted((a, b) => (a.priority < b.priority) ? -1 : (a.priority > b.priority) ? 1 : 0);
}

// The greatest id first, with sort on a copy.
export function newestFirst(tasks: ReadonlyArray<Task>): Task[] {
  return [...tasks].sort((a, b) => (a.id > b.id) ? -1 : (a.id < b.id) ? 1 : 0);
}

// A second key decides when the first keys are equal.
export function byPriorityThenName(tasks: ReadonlyArray<Task>): Task[] {
  return tasks.toSorted((a, b) =>
    (a.priority < b.priority) ? -1 : (a.priority > b.priority) ? 1 : (a.name < b.name) ? -1 : (a.name > b.name) ? 1 : 0);
}

// A key of a field of a field, with the tests in the other order.
export function byTaskName(entries: ReadonlyArray<Entry>): Entry[] {
  return entries.toSorted((x, y) => (y.task.name < x.task.name) ? 1 : (x.task.name < y.task.name) ? -1 : 0);
}

// The elements themselves are the keys.
export function ascending(xs: ReadonlyArray<bigint>): bigint[] {
  return [...xs, 0n].sort((x, y) => (x < y) ? -1 : (x > y) ? 1 : 0);
}

export function names(xs: ReadonlyArray<string>): string[] {
  return xs.toSorted((a: string, b: string) => (a < b) ? -1 : (a > b) ? 1 : 0);
}

interface Event {
  readonly time: number;
  readonly kind: string;
}

// A difference of number keys: the comparator is consistent when every key
// is finite.
export function chronological(events: ReadonlyArray<Event>): Event[] {
  return events.toSorted((a, b) => a.time - b.time);
}

export function latestFirst(events: ReadonlyArray<Event>): Event[] {
  return [...events].sort((a, b) => b.time - a.time);
}

// A difference as the last comparison of a chain.
export function byKindThenTime(events: ReadonlyArray<Event>): Event[] {
  return events.toSorted((a, b) => (a.kind < b.kind) ? -1 : (a.kind > b.kind) ? 1 : a.time - b.time);
}

// A comparison of number keys, which is consistent when no key is NaN.
export function numbers(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((x, y) => (x < y) ? -1 : (x > y) ? 1 : 0);
}
