// `const [a, , b, ...rest] = e` declares a name for each place of the array
// pattern. An empty place is a hole, and the rest element takes the rest.
export function f(xs: ReadonlyArray<bigint>, pair: [bigint, string]) {
  const [a, b] = xs;
  let [c] = xs;
  const [, d] = xs;
  let [e, , g] = xs;
  const [, , h, , i] = xs;
  const [first, ...others] = xs;
  let [...all] = xs;
  const [, ...tail] = xs;
  const [j, , ...k] = xs;
  const [n, s]: [bigint, string] = pair;
  let [m]: ReadonlyArray<bigint> = xs.filter((x) => x > 0n)
  const [p, q] = [1n, 2n];
  return [a, b, c, d, e, g, h, i, first, others, all, tail, j, k, n, s, m, p, q];
}

const [top, ...more] = [1, 2, 3];
