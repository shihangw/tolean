/** A stock line: how many units are on hand, and the most to order. */
export interface Line {
  readonly active: boolean;
  readonly onHand: bigint;
  readonly cap: bigint;
}

export interface Order {
  readonly amounts: ReadonlyArray<bigint>;
  readonly total: bigint;
}

/** What one line orders toward `wanted`: nothing, `wanted`, or its cap. */
export function orderFor(line: Line, wanted: bigint): bigint {
  if (!line.active) {
    return 0n;
  }
  return wanted < line.cap ? wanted : line.cap;
}

export function planOrder(lines: ReadonlyArray<Line>, wanted: bigint): Order {
  let left = wanted;
  let total = 0n;
  const amounts: Array<bigint> = [];
  for (const line of lines) {
    const amount = orderFor(line, left);
    amounts.push(amount);
    left -= amount;
    total += amount;
  }
  return { amounts, total };
}
