// expect: 3:10 === needs two values of the same primitive type
export function same<T>(a: T, b: T): boolean {
  return a === b;
}
