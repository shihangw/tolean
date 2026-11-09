// expect: 5:10 'Done' is not a member of the enum Status
enum Status { Active = 'active', Paused = 'paused' }

export function done(): Status {
  return Status.Done;
}
