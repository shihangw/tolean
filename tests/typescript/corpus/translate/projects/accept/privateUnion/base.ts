// A literal union that the file does not export, which an exported alias
// reaches through the field of a private interface.
type Level = 'low' | 'high';

interface Item {
  readonly level: Level;
}

export type Public = Item;
