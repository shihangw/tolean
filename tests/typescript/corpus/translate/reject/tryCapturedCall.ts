// expect: 8:3 try bodies allow only
export function refused(value: bigint): bigint {
  let current = value;
  function change(): bigint {
    current = 3n;
    return current;
  }
  try {
    return change();
  } catch (ignored) {
    return current;
  }
}
