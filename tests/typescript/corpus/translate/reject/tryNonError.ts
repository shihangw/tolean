// expect: 3:3 try bodies allow only
export function refused(): bigint {
  try {
    throw 1n;
  } catch (ignored) {
    return 2n;
  }
}
