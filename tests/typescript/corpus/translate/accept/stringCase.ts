/**
 * `toUpperCase` and `toLowerCase` on strings that the translator can show
 * are ASCII: literals, and `+`, `trim` and `slice` of them. On ASCII only
 * `a` to `z` and `A` to `Z` change, in every Unicode version.
 */
export function shout(): string {
  return "hello, world".toUpperCase();
}

export function quiet(): string {
  return (" ABC " + "Def").trim().toLowerCase();
}

export function head(): string {
  return "status".slice(0, 3).toUpperCase();
}

export function isOk(code: string): boolean {
  return code === "ok".toUpperCase();
}
