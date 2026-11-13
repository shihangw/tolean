// expect: 4:10 'padStart' to more than 268435440 code units could make a string that an engine refuses
// V8 throws a RangeError for a string this long; the model would not.
export function f(s: string): string {
  return s.padStart(300000000);
}
