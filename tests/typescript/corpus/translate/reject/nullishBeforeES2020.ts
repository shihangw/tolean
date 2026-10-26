// target: ES2019
// expect: 3:56 the target ES2019 does not have '??'
export function f(a: number | null): number { return a ?? 0; }
