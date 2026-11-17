// expect: 3:16 expected '('
export function refused(): bigint {
  try {} catch {}
  return 0n;
}
