// expect: 3:10 new Map takes at most one argument
export function f(): Map<string, bigint> {
  return new Map<string, bigint>([], []);
}
