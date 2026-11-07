// expect: 3:8 tsc may read this word and the name before it as the start of a declaration
function f(type: bigint): void {
  type as const;
}
