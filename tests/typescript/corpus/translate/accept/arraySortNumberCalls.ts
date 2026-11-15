// certify: required
interface Item {
  readonly value: number;
}

function sorted(items: ReadonlyArray<Item>): Item[] {
  return items.toSorted((a, b) => a.value - b.value);
}

// The list argument changes position in the forwarding chain.
function middle(_unused: boolean, values: ReadonlyArray<Item>): Item[] {
  return sorted(values);
}

export function outer(xs: ReadonlyArray<Item>): Item[] {
  return middle(true, xs);
}

function compared(values: ReadonlyArray<number>): number[] {
  return values.toSorted((a, b) => (a < b) ? -1 : (a > b) ? 1 : 0);
}

export function compare(xs: ReadonlyArray<number>): number[] {
  return compared([...xs]);
}
