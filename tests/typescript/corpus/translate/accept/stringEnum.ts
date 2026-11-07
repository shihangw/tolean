export enum Status {
  Active = 'active',
  Paused = 'paused',
  Done = 'done',
}

enum Level { Low = 'low', High = 'high' }

export function isActive(s: Status): boolean {
  return s === Status.Active;
}

export function next(s: Status): Status {
  if (s === Status.Active) {
    return Status.Paused;
  }
  if (s !== Status.Done) {
    return Status.Done;
  }
  return s;
}

export function level(n: bigint): Level {
  return n > 10n ? Level.High : Level.Low;
}

export function lastStatus(statuses: ReadonlyArray<Status>): Status | null {
  let last: Status | null = null;
  for (const s of statuses) {
    last = s;
  }
  return last;
}
