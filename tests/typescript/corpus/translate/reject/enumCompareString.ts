// expect: 5:10 === needs two values of the same primitive type
enum Status { Active = 'active', Paused = 'paused' }

export function isActive(s: Status): boolean {
  return s === 'active';
}
