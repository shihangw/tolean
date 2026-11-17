// expect: 3:3 the first catch subset must ignore its binding
export function refused(): bigint {
  try {
    throw new Error("first");
  } catch (Error) {
    throw new Error("second");
  }
}
