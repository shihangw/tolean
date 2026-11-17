export function caught(flag: boolean): bigint {
  try {
    if (flag) {
      throw new Error("caught");
    }
    return 1n;
  } catch (error) {
    return 2n;
  }
}

export function nested(): bigint {
  try {
    try {
      throw new Error("inner");
    } catch (inner) {
      throw new Error("outer");
    }
  } catch (outer) {
    return 3n;
  }
}
