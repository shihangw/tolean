// expect: 3:1 'NaN' would hide the global NaN
// A function named NaN would hide the global that the subset reads.
export function NaN(): bigint {
  return 1n;
}
