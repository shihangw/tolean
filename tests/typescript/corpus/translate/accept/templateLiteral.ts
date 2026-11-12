/**
 * A template literal reads as `+` on strings: `` `a${e}b` `` is
 * `("a" + (e) + "b")`. Both convert each substitution with ToString, so a
 * part may be a string, a number, a bigint or a boolean, and a template
 * without substitutions is a string.
 */
export interface User {
  readonly name: string;
  readonly age: number;
  readonly admin: boolean;
}

export function greet(u: User): string {
  return `Hello, ${u.name}!`;
}

export function describe(u: User, visits: bigint): string {
  return `${u.name} (${u.age}) has ${visits} visits; admin: ${u.admin}`;
}

export function plain(): string {
  return `no substitutions`;
}

export function nested(a: string, b: string): string {
  return `[${a.length > 0 ? `${a}:${b}` : b}]`;
}

export function lines(n: number): string {
  return `first
second ${n}`;
}

export function escapes(s: string): string {
  return `\`${s}\` costs \${0} \u{1F600}`;
}

export function inLoop(xs: ReadonlyArray<string>): string {
  let out = ``;
  for (const x of xs) {
    out += `<${x}>`;
  }
  return out;
}
