// expect: 4:1 tsc may read this token after 'as const' as a part of the type
function f(y: bigint): void {
  const x = y as const
[0];
}
