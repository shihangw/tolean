// expect: 4:3 'Swap' may refer to itself only with its own type parameters, in order
export interface Swap<A, B> {
  readonly a: A;
  readonly next: Swap<B, A> | null;
}
