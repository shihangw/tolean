// expect: 3:3 the first catch subset must ignore its binding
export function refused(): boolean {
  try {
    throw new Error("first");
  } catch (error) {
    return error instanceof Error;
  }
}
