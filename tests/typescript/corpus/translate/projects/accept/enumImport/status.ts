// An exported string enum, and a function that reads its members.
export enum Status {
  Active = 'active',
  Paused = 'paused',
  Done = 'done',
}

export function pause(s: Status): Status {
  if (s === Status.Active) return Status.Paused;
  return s;
}
