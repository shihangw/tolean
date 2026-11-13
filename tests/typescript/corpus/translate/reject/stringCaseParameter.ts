// expect: 4:10 'toUpperCase' is supported only on a string that is ASCII
// The result on "é" or "ß" follows the Unicode version of the engine.
export function shout(s: string): string {
  return s.toUpperCase();
}
