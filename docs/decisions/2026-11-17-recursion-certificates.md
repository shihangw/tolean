# Keep recursion out of certificates for now

The translator may emit recursive Lean definitions when Lean proves that each
recursive call decreases structurally. It may also emit finite recursive
structures. The
generated definitions use ordinary function calls, which ECMA-262 specifies
with `EvaluateCall` (§13.3.6.2 in ES2024). TypeScript interfaces and aliases
erase before execution, so recursive types add no runtime operation or edition
gate.

`program_sound` covers these translated programs. A certificate does not cover
them yet. A recursive interface needs an encoder and decoder that recurse
through nested lists and optional fields, plus a reusable proof that decoding
the encoding returns the original value. A recursive function also needs a
certificate whose interpreter fuel can grow with each recursive call. The
current certificate theorem uses one fixed call-depth bound. The library has
no lemma that proves more interpreter fuel preserves a successful result, so
it cannot compose existential bounds safely.

Keep recursive interfaces and functions refused by `tolean certify` until both
proofs exist. Continue to accept only recursion for which Lean itself proves
termination. The translator accepts a self-referential interface and a
single-function structural call only when its checks and Lean's termination
checker accept them. It does not emit a recursive tagged union as one mutual
type block, so keep that form refused. Do not accept a user-supplied measure,
mutual recursion, or a `while` loop as a substitute: the translator has no
checked measure obligation for those forms. These limits affect certificates
and translation separately. They do not weaken `program_sound` or allow a
partial definition.
