export function slice(s: string, i: number): string {
  return s.slice(i);
}
export function starts(s: string, i: number): boolean {
  return s.startsWith("a", i);
}
export function ends(s: string, i: number): boolean {
  return s.endsWith("a", i);
}
export function includes(s: string, i: number): boolean {
  return s.includes("a", i);
}
export function index(s: string, i: number): number {
  return s.indexOf("a", i);
}
export function charAtIndex(s: string, i: number): string {
  return s.at(i) ?? "";
}
export function bounds(s: string, i: number, j: number): string {
  return s.slice(i, j);
}
export function split(s: string, i: number): ReadonlyArray<string> {
  return s.split("a", i);
}
