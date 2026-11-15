export interface Box<T> {
  value: T;
  extra?: T;
}

export function read(p: Box<bigint>): bigint {
  return p.value + (p.extra ?? 0n);
}
