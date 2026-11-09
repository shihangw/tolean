// expect: 3:3 'T' would hide the type parameter T in Lean; choose another name
interface Box<T> {
  readonly T: T;
}
