// Counted for loops: a declaration or nothing, then a test and an update,
// each of which may be absent.
export function sum(n: number): number {
  let s = 0;
  for (let i = 0; i < n; i++) {
    s += i;
  }
  for (let i: number = n; i > 0; i -= 2) s += i;
  for (const k = 1; ; ) {
    break;
  }
  for (;;) {
    continue;
  }
  for (let j; ; j = 1) ;
  for (let of = 0; of < 1; of++) {}
  for (let i = 0;
    i < n;
    i++) {}
  return s;
}

// An `in` in the declaration stands in parentheses, braces, the arguments of a
// call or an index, or in the middle of a conditional. The test and the update
// may use it anywhere.
export function brackets(o: object, c: boolean): void {
  for (let a = ('k' in o); ; ) break;
  for (let b = [('k' in o)]; ; ) break;
  for (let d = { k: 'k' in o }; ; ) break;
  for (let e = f('k' in o); ; ) break;
  for (let g = o['k' in o]; ; ) break;
  for (let h = c ? 'k' in o : false; ; ) break;
  for (let x = 0; 'k' in o; ) break;
  for (; ; 'k' in o) break;
}
