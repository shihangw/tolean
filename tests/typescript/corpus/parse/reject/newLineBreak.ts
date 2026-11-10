// expect: 4:5 tsc may read this '<' as the start of type arguments
export function f() {
  return new Map
    <string, bigint>();
}
