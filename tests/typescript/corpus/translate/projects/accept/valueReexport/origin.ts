export enum Color { Red = "red", Blue = "blue" }

export function double(n: bigint): bigint {
  return n * 2n;
}

export function isRed(c: Color): boolean {
  return c === Color.Red;
}
