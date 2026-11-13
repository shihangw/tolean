/** `new Set(s)` adds each code point of the string `s`, in order. */
export function distinct(s: string): Set<string> {
  return new Set<string>(s);
}

export function hasRepeat(s: string): boolean {
  return new Set<string>(s).size !== [...s].length;
}
