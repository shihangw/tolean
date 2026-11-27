export function put(m: Map<string, bigint>, k: string): void {
  m.set(k, 1n);
}
