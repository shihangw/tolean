// expect: 4:20 arrow functions with a body in braces are not supported
export function f(): bigint {
  let n = 0n;
  const add = x => {
    n += x;
  };
  add(1n);
  return n;
}
