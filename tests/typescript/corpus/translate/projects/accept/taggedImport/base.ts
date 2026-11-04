// An exported tagged union whose member interfaces the file does not export.
interface Circle {
  readonly kind: 'circle';
  readonly r: bigint;
}

interface Square {
  readonly kind: 'square';
  readonly side: bigint;
}

export type Shape = Circle | Square;
