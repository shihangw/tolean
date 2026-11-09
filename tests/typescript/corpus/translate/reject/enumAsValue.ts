// expect: 5:13 only parameters and locals may be referenced
enum Status { Active = 'active' }

export function f(): Status {
  const s = Status;
  return s.Active;
}
