// Local functions. A function that returns nothing changes `let` locals of
// the function around it: the output lifts it out, passes it the locals its
// body names, and binds the ones it changes again after each call, in a loop
// too. A function that returns a value reads the locals around it.
export interface Event {
  readonly amount: bigint;
  readonly deposit: boolean;
}

export function balance(events: ReadonlyArray<Event>, fee: bigint): bigint {
  let total = 0n;
  let count = 0n;
  function apply(amount: bigint): void {
    total += amount - fee;
    count += 1n;
  }
  for (const e of events) {
    if (e.deposit) {
      apply(e.amount);
    } else {
      apply(-e.amount);
    }
  }
  return total * count;
}

export function scaled(xs: ReadonlyArray<bigint>, k: bigint): bigint {
  let last = 0n;
  function scale(x: bigint): bigint {
    return x * k;
  }
  function remember(x: bigint): void {
    last = x;
  }
  for (const x of xs) {
    const y = scale(x);
    remember(y);
  }
  return scale(last);
}

export function clamp(x: bigint, lo: bigint, hi: bigint): bigint {
  function below(): boolean {
    if (x < lo) {
      return true;
    }
    return false;
  }
  const small = below();
  if (small) return lo;
  return x > hi ? hi : x;
}
