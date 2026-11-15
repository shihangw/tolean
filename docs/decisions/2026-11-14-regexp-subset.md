# Model regular expressions with ordered backtracking

**Status:** accepted design; implementation pending · **Date:** 2026-11-14

Tolean will model the first TypeScript regular expressions with the
continuation-passing matcher of ECMA-262 §22.2.2. The order in which it tries
alternatives is part of the result. A language-membership matcher alone
cannot specify captures or replacement.

This decision answers the open questions in
[#218](https://github.com/shihangw/tolean/issues/218). It does not add regular
expressions to the accepted subset.

## Start without flags

The first version accepts no flags. It refuses `i`, `g`, `m`, `s`, `u`, `y`,
`d` and `v`, rather than ignoring them. Global and sticky matching change
`lastIndex`, so they need a separate account of object state.

The model works on UTF-16 code units. The existing
[`JSString` decision](2026-11-06-jsstring.md) and implementation already use
code units, not code points. Thus the absence of `u` fits the current model.
For example, `/^.$/` must not match an astral character represented by two
code units. The `u` flag is future work, because it changes both how patterns
are read and how the matcher advances through a string.

Without `s`, a dot excludes LF, CR, U+2028 and U+2029. Without `m`, the
anchors test the beginning and end of the input. The matcher must not borrow
another engine's rule that permits `$` before a final line break.

## Keep the first grammar explicit

The first grammar includes literal characters, character classes with ranges
and negation, dot, alternatives, capturing groups and `(?:...)` groups. It
also includes `^`, `$` and the greedy quantifiers `*`, `+`, `?`, `{n}`,
`{n,}` and `{n,m}`. The parser checks that a finite maximum is not smaller
than its minimum.

Character escapes enter the subset only with their exact character sets.
Without flags, `\d` is ASCII digits and `\w` is ASCII letters, digits and
underscore. `\s` needs the WhiteSpace and LineTerminator sets of the target
edition, not a host library's whitespace predicate. Unsupported escapes
remain errors rather than being interpreted as literal text.

Lazy quantifiers, backreferences, lookaround, named groups and constructor
calls remain refused. The parser must distinguish a literal slash from
division with the syntactic context that TypeScript uses. A rule that looks
only at the preceding token is insufficient: a closing parenthesis can end
either an expression or an `if` condition. Tests must compare these contexts
with `tsc`, including comments and escaped slashes in character classes.

## Preserve priority and prove progress

The matcher tries an alternative on the left before one on the right.
A greedy quantifier tries another repetition before the continuation that
follows the quantifier. A failed continuation must permit backtracking.
Captures belong to a candidate state, so failure must restore the previous
state rather than retaining captures from a rejected path.

RepeatMatcher in §22.2.2.3.1 rejects a repetition that leaves the input
position unchanged when the remaining minimum is zero. Before that minimum
reaches zero, an empty repetition may succeed, but it decreases the minimum.
Afterwards, each successful recursive repetition consumes at least one code
unit. This gives a local decreasing measure: the remaining minimum plus
the remaining input length. A finite maximum decreases too.

That local measure does not by itself prove termination of an entire
continuation-passing matcher. A continuation may resume an enclosing
quantifier or try another alternative. The implementation must account for
those calls, either with well-founded recursion over its explicit search
state or with fuel and a proof that the chosen bound suffices. Exponential
backtracking is allowed; no claim of linear running time is made.

If a sufficient bound is not proved, exhaustion must be distinct from
failure to match. It must not yield `false`, `null` or an unchanged string.
In that case, only a conditional value claim is permitted, as for recursion:
when evaluation returns a value, it agrees with the spec. The translation
must refuse a program unless its generated result and soundness theorem
preserve that distinction. A fixed unproved budget is not an implementation
of a total boolean `test`.

## Deliver the methods separately

The first translated call is `r.test(s)` where `r` is a literal pattern and
`s` is a string. Its edition entry cites ECMA-262 §22.2, including the
Pattern semantics and the algorithms for `test` and RegExpBuiltinExec.
The search tries successive starting positions in order, including the end
of the input so that an empty pattern can match there.

Next comes `s.match(r)` without `g`. Failure is `null`. Success includes the
whole match followed by the captures, and a capture that did not participate
is `undefined`, not an empty string. Repetition must clear the captures
inside its atom as the spec requires. Translation must refuse uses that
need an optional element type until that type is supported. Result
properties such as `index`, `input` and `groups` require their own
representation before programs can read them.

Replacement comes in a separate change. `s.replace(r, replacement)` replaces
only the first match, and the initial version accepts only a literal
replacement string with no dollar sign. This conservative restriction
avoids silently treating substitution patterns as literal text. Replacement
callbacks and dollar substitutions remain future work.

Each method must extend the interpreter and IR evaluator together, and keep
`program_sound` proved. Node comparisons must cover randomized patterns and
inputs as well as fixed cases for backtracking, empty repetitions, captures,
line terminators and surrogate code units. Parser round trips and existing
translation output must remain unchanged for already accepted programs.

## Do not share a matcher across languages yet

Go's RE2 semantics and SQL's pattern operations do not specify the same
ordered captures as JavaScript. Neither translator will use this model in
the first version. A later shared representation would need a separate
correctness argument for each language.

Tolean will not add Mathlib or another dependency. A theorem that relates
the regular fragment to Mathlib's `RegularExpression` is future work outside
this implementation. Such a theorem would concern membership, not by itself
the order of captures or replacement results.
