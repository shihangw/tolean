// expect: 3:10 'includes' does not take a callback here
export function f(s: string): boolean {
  return s.includes((c) => c);
}
