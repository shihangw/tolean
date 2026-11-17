// expect: 3:3 try bodies allow only
export function refused(value: bigint): bigint {
  try {
    value = 3n;
    throw new Error("changed");
  } catch (ignored) {
    return value;
  }
}
