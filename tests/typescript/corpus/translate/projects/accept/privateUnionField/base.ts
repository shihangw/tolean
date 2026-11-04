// A literal union that the file does not export, which an exported
// interface names in a field and an exported alias names directly.
type Status = 'open' | 'closed';

export interface Ticket {
  readonly status: Status;
}

export type PublicStatus = Status;
