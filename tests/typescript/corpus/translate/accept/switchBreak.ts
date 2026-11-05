interface Deposit {
  readonly type: 'deposit';
  readonly amount: bigint;
}

interface Withdraw {
  readonly type: 'withdraw';
  readonly amount: bigint;
}

interface Freeze {
  readonly type: 'freeze';
}

export type Event = Deposit | Withdraw | Freeze;

// A fold over events, as a reducer writes it.
export function balance(events: ReadonlyArray<Event>): bigint {
  let total = 0n;
  let frozen = false;
  for (const e of events) {
    switch (e.type) {
      case 'deposit':
        if (!frozen) {
          total += e.amount;
        }
        break;
      case 'withdraw':
        total -= e.amount;
        break;
      case 'freeze':
        frozen = true;
        break;
    }
  }
  return total;
}

// A default takes the members that no case names, and the last clause may
// leave out its break.
export function weight(e: Event): bigint {
  let w = 1n;
  switch (e.type) {
    case 'freeze':
      w = 0n;
      break;
    default:
      w = 2n;
  }
  return w;
}

// Without a default, the members that no case names keep the locals as they are.
export function deposits(e: Event, n: bigint): bigint {
  let count = n;
  switch (e.type) {
    case 'deposit':
      count += 1n;
      break;
  }
  return count;
}
