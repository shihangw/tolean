// expect: 5:10 a value of the enum Status is one of its members
enum Status { Active = 'active', Paused = 'paused' }

export function first(): Status {
  return 'active';
}
