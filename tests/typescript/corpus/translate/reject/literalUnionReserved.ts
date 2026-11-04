// expect: 2:1 'rec' cannot name a Lean constructor; a literal union needs strings such as 'open'
type T = 'rec' | 'b';
