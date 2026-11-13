// expect: 3:10 JSON.stringify takes one value here; a replacer and an indent are not supported
export function render(s: string): string {
  return JSON.stringify(s, null, 2);
}
