// expect: 3:3 try and catch must end the function
export function refused(): bigint {
  try {} catch (ignored) {}
  return 1n;
}
