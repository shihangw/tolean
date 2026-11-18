// expect: 3:10 only new Date(t), new Map() and new Set() are supported
export function prototype(): string {
  return new Error("message").__proto__;
}
