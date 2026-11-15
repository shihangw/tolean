// certify: required
interface Item {
  readonly name: string;
  readonly rank: number;
  readonly time: number;
  readonly id: bigint;
}
export function rankThenTime(xs: ReadonlyArray<Item>): Item[] {
  return xs.toSorted((a, b) => (a.rank < b.rank) ? -1 : (a.rank > b.rank) ? 1 : a.time - b.time);
}
export function nameThenTime(xs: ReadonlyArray<Item>): Item[] {
  return xs.toSorted((a, b) => (a.name < b.name) ? -1 : (a.name > b.name) ? 1 : b.time - a.time);
}
export function rankThenId(xs: ReadonlyArray<Item>): Item[] {
  return [...xs].sort((a, b) => (a.rank > b.rank) ? -1 : (a.rank < b.rank) ? 1 : (a.id < b.id) ? -1 : (a.id > b.id) ? 1 : 0);
}
export function forwarded(xs: ReadonlyArray<Item>): Item[] {
  return rankThenTime(xs);
}
export function threeKeys(xs: ReadonlyArray<Item>): Item[] {
  return xs.toSorted((a, b) => (a.rank < b.rank) ? -1 : (a.rank > b.rank) ? 1 : (a.name > b.name) ? -1 : (a.name < b.name) ? 1 : a.time - b.time);
}
