// expect: 3:3 try bodies allow only
export function refused(value: bigint): string {
  try {
    return JSON.stringify(value);
  } catch (ignored) {
    return "caught";
  }
}
