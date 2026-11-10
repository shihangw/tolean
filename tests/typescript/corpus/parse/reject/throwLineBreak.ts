// expect: 4:3 a line break after 'throw'
export function f(): bigint {
  throw
  1n;
}
