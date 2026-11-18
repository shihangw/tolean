// certify: required
export interface Pair {
  readonly a: bigint;
  readonly b: bigint;
}

export type Key = "pair" | "other";
export type Envelope = Record<Key, Pair>;

export function inCatch(pair: Pair, fail: boolean): bigint {
  try {
    if (fail) {
      throw new Error("recover");
    }
    return 7n;
  } catch (ignored) {
    const { a: first, b: second } = pair;
    return first + second;
  }
}

export function fromIndex(envelope: Envelope): bigint {
  const pair = envelope["pair"];
  const { a, b } = pair;
  return a - b;
}
