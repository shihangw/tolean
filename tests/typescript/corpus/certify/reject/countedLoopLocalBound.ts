// expect: counted loop bounds must read only function parameters

export function sum(limit: number): number {
  const end = limit;
  let total = 0;
  for (let i = 0; i < end; i++) total += i;
  return total;
}
