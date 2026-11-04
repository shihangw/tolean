import type { PublicStatus, Ticket } from "./base.ts";

export function isOpen(t: Ticket): boolean {
  return t.status === 'open';
}

export function opened(): PublicStatus {
  return 'open';
}
