export type Shape =
  | { readonly kind: 'circle'; readonly r: number }
  | { readonly kind: 'square'; readonly side: number };

export function size(s: Shape): number {
  switch (s.kind) {
    case 'circle':
      return s.r;
    case 'square':
      return s.side;
  }
}

export function circle(r: number): Shape {
  return { kind: 'circle', r };
}

export type Range = { readonly lo: number; readonly hi: number };

export function pair(a: number): { readonly lo: number; readonly hi: number } {
  return { lo: a, hi: a + 1 };
}

export function area(box: { readonly w: number; readonly h: number }): number {
  return box.w * box.h;
}

export interface Segment {
  readonly start: { readonly x: number; readonly y: number };
  readonly items: ReadonlyArray<{ readonly n: number }>;
}

export function startX(segment: Segment): number {
  return segment.start.x;
}

export function segment(x: number, y: number): Segment {
  return { start: { x, y }, items: [{ n: x }] };
}

export type On = { readonly kind: 'on'; readonly value: bigint };
export interface Off {
  readonly kind: 'off';
}
export type Switch = On | Off;

export function state(s: Switch): bigint {
  switch (s.kind) {
    case 'on':
      return s.value;
    case 'off':
      return 0n;
  }
}
