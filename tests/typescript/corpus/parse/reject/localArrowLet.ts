// expect: 4:24 return types of arrow functions are not supported
export function f(): bigint {
  let n = 0n;
  let add = (x: bigint): void => {
    n += x;
  };
  add(1n);
  return n;
}
