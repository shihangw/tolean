// certify: required
export function mapped(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b).map(x => x + 1);
}
export function chosen(xs: ReadonlyArray<number>, ys: ReadonlyArray<number>, flag: boolean): number[] {
  return flag ? xs.toSorted((a, b) => a - b) : ys.toSorted((a, b) => b - a);
}
export function bound(xs: ReadonlyArray<number>): number[] {
  const ys = xs.toSorted((a, b) => a - b);
  return ys.map(x => x + 1);
}
export function mappedInput(xs: ReadonlyArray<number>): number[] {
  return xs.map(x => x + 1).toSorted((a, b) => a - b);
}
export function filteredInput(xs: ReadonlyArray<number>): number[] {
  return xs.filter(x => x > 0).toSorted((a, b) => a - b);
}
export function sliced(xs: ReadonlyArray<number>): number[] {
  return xs.slice(1).toSorted((a, b) => a - b);
}
export function slicedAt(xs: ReadonlyArray<number>, n: number): number[] {
  return xs.slice(n).toSorted((a, b) => a - b);
}
export function called(xs: ReadonlyArray<number>): number[] {
  return mappedInput(xs).toSorted((a, b) => b - a);
}
export function selectedInput(xs: ReadonlyArray<number>, ys: ReadonlyArray<number>, flag: boolean): number[] {
  return (flag ? xs : ys).toSorted((a, b) => a - b);
}
export function composed(xs: ReadonlyArray<number>): number[] {
  const ys = xs.map(x => x + 1).filter(x => x > 0).slice(1);
  return ys.toSorted((a, b) => b - a).map(x => x + 1);
}
