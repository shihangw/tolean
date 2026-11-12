// expect: 5:3 after an if whose first branch ends in a return, a throw, a break or a continue, put the code that follows in its else branch
// The first branch throws, the else branch runs on, and so do the statements after the if.
export function f(c: boolean, n: bigint): bigint {
  let x = n;
  if (c) {
    throw new Error("c");
  } else {
    x = 1n;
  }
  x = x + 1n;
  return x;
}
