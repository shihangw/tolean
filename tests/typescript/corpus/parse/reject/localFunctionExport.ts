// expect: 3:3 'export' is not supported here
export function f(): void {
  export function g(): void {}
}
