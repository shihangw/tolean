// expect: 4:10 'toUpperCase' is supported only on a string that is ASCII
// "ß" becomes "SS", and other letters change with the Unicode version.
export function shout(): string {
  return "straße".toUpperCase();
}
