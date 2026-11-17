// certify: required
export function recover(flag: boolean, original: bigint): bigint {
  try {
    const value = original;
    if (flag) {
      throw new Error("caught");
    }
    return value;
  } catch (ignored) {
    return 7n;
  }
}

export function entryScope(original: bigint): bigint {
  try {
    const detail = "caught";
    throw new Error(detail);
  } catch (ignored) {
    return original;
  }
}

export function returnSkipsCatch(original: bigint): bigint {
  try {
    return original;
  } catch (ignored) {
    throw new Error("unreachable handler");
  }
}

export function handlerThrows(): bigint {
  try {
    throw new Error("first");
  } catch (ignored) {
    throw new Error("handler");
  }
}

export function returningBranch(flag: boolean): bigint {
  if (flag) {
    try {
      throw new Error("branch");
    } catch (ignored) {
      return 11n;
    }
  } else {
    return 13n;
  }
}
