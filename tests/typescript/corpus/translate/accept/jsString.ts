/** Plain strings. Each is a `JSString`, the list of its UTF-16 code units. */
export interface User {
  readonly name: string;
  readonly nick: string | null;
}

/** A character above U+FFFF is two code units, a surrogate pair. */
export function greeting(admin: boolean): string {
  return admin ? "héllo 😀" : "";
}

export function isRoot(u: User): boolean {
  return u.name === "root";
}

export function differ(a: User, b: User): boolean {
  return a.name !== b.name;
}

export function nickOr(u: User): string {
  return u.nick ?? u.name;
}

export function rename(u: User, name: string): User {
  return { name: name, nick: u.nick };
}

export function names(users: ReadonlyArray<User>): ReadonlyArray<string> {
  const out: string[] = [];
  for (const u of users) {
    if (u.name !== "") {
      out.push(u.name);
    }
  }
  return out;
}
