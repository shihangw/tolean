type Id = bigint;
type Ids = ReadonlyArray<Id>;
export type Score = number | null;

export interface Player {
  readonly id: Id;
  readonly score: Score;
}

export function total(ids: Ids): Id {
  let sum = 0n;
  for (const id of ids) {
    sum += id;
  }
  return sum;
}

export function hasScore(p: Player): boolean {
  return p.score !== null;
}

export function reset(p: Player): Player {
  const cleared: Score = null;
  return { id: p.id, score: cleared };
}
