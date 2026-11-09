// expect: 5:10 the value does not have the function's return type
enum Status { Active = 'active' }

export function f(): string {
  return Status.Active;
}
