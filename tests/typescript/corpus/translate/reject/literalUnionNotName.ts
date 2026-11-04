// expect: 2:1 'in progress' cannot name a Lean constructor; a literal union needs strings such as 'open'
type T = 'in progress' | 'done';
