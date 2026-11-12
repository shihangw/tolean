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
  return [...xs].sort((x, y) => (x < y) ? -1 : (x > y) ? 1 : 0);
}

export function names(xs: ReadonlyArray<string>): string[] {
  return xs.toSorted((a: string, b: string) => (a < b) ? -1 : (a > b) ? 1 : 0);
}
