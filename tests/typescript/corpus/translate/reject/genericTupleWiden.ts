// expect: 3:10 the value does not have the function's return type
export function lift<T>(p: [T, T]): [T | null, T] {
  return p;
}
