// An exported alias of an interface that the file does not export, whose
// field is another interface that it does not export either.
interface Deep {
  readonly d: bigint;
}

interface Internal {
  readonly value: bigint;
  readonly deep: Deep;
}

export type Public = Internal;
