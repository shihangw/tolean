// expect: 3:10 expected 'catch'
export function refused(): bigint {
  try {} finally {}
  return 0n;
}
