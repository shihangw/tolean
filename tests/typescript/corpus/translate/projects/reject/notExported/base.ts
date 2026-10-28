function hidden(): bigint {
  return 1n;
}

export function f(): bigint {
  return hidden();
}
