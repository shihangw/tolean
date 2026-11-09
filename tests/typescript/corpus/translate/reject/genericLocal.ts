// expect: 3:3 'T' would hide the type parameter T in Lean; choose another name
export function f<T>(x: T): T {
  const T = 1n;
  return x;
}
