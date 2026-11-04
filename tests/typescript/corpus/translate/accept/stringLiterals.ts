export type Status = 'open' | 'closed' | 'in_review';
type Priority = 'low' | 'high';

export interface Ticket {
  readonly id: bigint;
  readonly status: Status;
}

export function isOpen(t: Ticket): boolean {
  return t.status === 'open';
}

export function close(t: Ticket): Ticket {
  return { id: t.id, status: 'closed' };
}

export function urgent(p: Priority | null): boolean {
  return p !== null && 'high' === p;
}

export function statusOf(done: boolean, reviewing: boolean): Status {
  let s: Status = done ? 'closed' : 'open';
  if (reviewing) {
    s = 'in_review';
  }
  return s;
}

export function countOpen(ts: ReadonlyArray<Ticket>): bigint {
  let n = 0n;
  for (const t of ts) {
    if (t.status !== 'closed') {
      n += 1n;
    }
  }
  return n;
}

export function lastStatus(ts: ReadonlyArray<Ticket>): Status {
  let s: Status = 'open';
  for (const t of ts) {
    if (s !== 'closed') {
      s = t.status;
    }
  }
  return s;
}

export interface Flag {
  readonly level: Priority | null;
}

export function isHigh(f: Flag): boolean {
  return f.level !== null;
}
