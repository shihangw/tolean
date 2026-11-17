// expect: 4:3 the first catch subset must ignore its binding
class C extends Error {}
export function refused(): bigint {
  try {
    throw new Error("first");
  } catch (C) {
    throw new C("second");
  }
}
