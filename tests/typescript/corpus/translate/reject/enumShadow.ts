// expect: 5:3 'Status' would hide the enum Status
enum Status { Active = 'active' }

export function f(): boolean {
  const Status = true;
  return Status;
}
