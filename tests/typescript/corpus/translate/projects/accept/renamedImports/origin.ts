export enum Color { Red = "red", Blue = "blue" }

export function double(n: bigint): bigint {
  return n * 2n;
}

function triple(n: bigint): bigint {
  return n * 3n;
}

// A local export list may rename a function, and may export an exported
// function under one more name.
export { triple as thrice, double as twice };
