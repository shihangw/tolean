// Arrow functions whose body is an expression.
export const id = (a) => a
export const inc = x => x + 1
export const none = () => 0
export const add = (a: number, b: number) => a + b
export const first = (xs: ReadonlyArray<string>, n: number | null) => xs[0]
export const nested = (a: bigint) => (b: bigint) => a * b
export const pick = (c: boolean) => c ? (x: number) => x : y => -y
export const obj = (k: string) => ({ k })
export const paren = ((a) => a)
export const assigns = (o: Point) => o.x = 1
export const chained = async => async

export function apply(xs: number[]): number {
  const g = (x: number) => x * 2;
  call(xs, (a, b) => a < b, x => x.length);
  return g(xs[0]);
}
