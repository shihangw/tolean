// expect: 3:10 only new Date(t), new Map() and new Set() are supported
export function stack(): string | undefined {
  return new Error("message").stack;
}
