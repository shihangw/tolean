// expect: 2:58 '>>>' needs two numbers, and JS throws a TypeError for it on bigints
export function f(a: bigint, b: bigint): bigint { return a >>> b; }
