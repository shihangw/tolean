export function between(a: bigint, b: bigint, c: bigint, d: bigint): boolean {
  return a < b && c > d;
}

export function bounded(x: bigint, n: bigint): boolean {
  return x < n && n > 0n;
}

export function outside(a: bigint, b: bigint, c: bigint, d: bigint): boolean {
  return a < b || c > d;
}

export function add(a: number, b: number, c: number, d: number): boolean {
  return a < b + c === d > 0;
}

export function multiply(a: number, b: number, c: number, d: number): boolean {
  return a < b * c === d > 0;
}

export function divide(a: number, b: number, c: number, d: number): boolean {
  return a < b / c === d > 0;
}

export function equal(a: number, b: number, c: number, d: number): boolean {
  return a < b === c > d;
}

export function unequal(a: number, b: number, c: number, d: number): boolean {
  return a < b !== c > d;
}

export function t(p: boolean, q: number, r: number, s: number, u: number): boolean {
  return p === q < r === s > u;
}
