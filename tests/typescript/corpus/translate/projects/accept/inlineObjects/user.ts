import { box, point } from "./data.ts";

export function id<T>(x: { readonly value: T }): { readonly value: T } {
  return box(x.value);
}

export function make(n: number): { readonly n: number } {
  return { n };
}

export function read(n: number): number {
  return point(n).n + make(n).n;
}

export type Wrapped<T> = { readonly child: { readonly value: T } };

export function wrap<T>(value: T): Wrapped<T> {
  return { child: box(value) };
}
