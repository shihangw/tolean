export type Fruit = 'apple' | 'pear';

export type Stock = Record<Fruit, bigint>;

export function restock(s: Stock): Stock {
  return { apple: s.apple + 1n, pear: s.pear + 1n };
}
