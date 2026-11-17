type Mixed = string | bigint;
type MaybeText = string | null;

export function isText(value: Mixed): value is string {
  return typeof value === "string";
}

export function typeofInTry(value: Mixed): string {
  try {
    if (typeof value === "string") return value;
    throw new Error("not text");
  } catch (ignored) {
    return "fallback";
  }
}

export function nullTestInTry(value: MaybeText): string {
  try {
    if (value !== null) return value;
    throw new Error("absent");
  } catch (ignored) {
    return "fallback";
  }
}

export function typeofInCatch(value: Mixed): string {
  try {
    throw new Error("retry");
  } catch (ignored) {
    if (typeof value === "string") return value;
    return "fallback";
  }
}

export function nullTestInCatch(value: MaybeText): string {
  try {
    throw new Error("retry");
  } catch (ignored) {
    if (value !== null) return value;
    return "fallback";
  }
}

export function checkedGuardInCatch(value: Mixed): string {
  try {
    throw new Error("retry");
  } catch (ignored) {
    if (isText(value)) return value;
    return "fallback";
  }
}
