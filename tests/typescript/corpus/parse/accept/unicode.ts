// Columns count code points. U+2028 ends a line, also inside a string.
export const smile = '😀😀' + "é"
export const separated = 'a b'
export const escaped = '\u{1F600}😀\x41B\'\"\\\0'
export const continued = 'one \
two'
export const after = smile + separated
