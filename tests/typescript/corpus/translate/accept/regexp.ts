export function backtrack(s: string): boolean {
  const r = /(?:^(a|ab)+c$)/;
  return r.test(s);
}

export function emptyRepeat(s: string): boolean {
  return /(?:(?:){3,})/.test(s);
}

export function codeUnit(s: string): boolean {
  return /(?:^.$)/.test(s);
}

export function repeatedTest(s: string): boolean {
  const r = /(?:a$)/;
  const alias = r;
  return r.test(s) && alias.test(s);
}

export function choosePattern(s: string, b: boolean): boolean {
  let r = /(?:a)/;
  if (b) r = /(?:b)/;
  return r.test(s);
}

export function whitespace(s: string): boolean {
  return /(?:^\s+$)/.test(s);
}
