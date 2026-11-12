// A `Date` from a time value, its UTC getters, and `Date.UTC`. The subset has
// no setters, so a date never changes, and a value stands for it.
interface Event {
  readonly name: string;
  readonly when: Date;
}

export function year(e: Event): number { return e.when.getUTCFullYear(); }

export function epoch(t: number): Date { return new Date(t); }

export function isValid(d: Date): boolean { return !Number.isNaN(d.getTime()); }

export function dayOfWeek(t: number): number { return new Date(t).getUTCDay(); }

export function midnight(y: number, m: number, d: number): number { return Date.UTC(y, m, d); }

export function later(a: Date, b: Date): boolean { return a.getTime() > b.valueOf(); }

export function secondsOfDay(d: Date): number {
  return d.getUTCHours() * 3600 + d.getUTCMinutes() * 60 + d.getUTCSeconds();
}

export function parts(d: Date): number[] {
  return [d.getUTCMonth(), d.getUTCDate(), d.getUTCMilliseconds()];
}
