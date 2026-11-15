# Model regular expressions with ordered backtracking

**Status:** accepted design; implementation pending · **Date:** 2026-11-14

Tolean will model the first TypeScript regular expressions with the
continuation-passing matcher of ECMA-262 §22.2.2. The order in which it tries
alternatives is part of the result. A language-membership matcher alone
cannot specify captures or replacement.

This decision answers the open questions in
[#218](https://github.com/shihangw/tolean/issues/218). The matcher and literal
parser implement the first part; regular expression calls are not yet
translated.

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

Lazy quantifiers, backreferences, lookaround and named groups remain refused.
The translator also refuses constructor calls.

## Give literals an unambiguous lexical boundary

The first accepted literals must begin with a non-capturing group:
`/(?:PATTERN)/` or `/(?:)PATTERN/`. Wrapping a pattern this way changes neither
its matching behavior nor its capture numbering. The prefix `/(?:` cannot
be division followed by an expression, so the lexer recognizes it without
guessing a lexical goal from the preceding token. Ordinary `/PATTERN/`
literals receive an explicit refusal.

Before a regex statement, the preceding simple statement must have a
written semicolon. Otherwise a slash on the next line could continue an
expression as division; accepting it as a new literal would insert a
semicolon that JavaScript does not insert.

This restriction preserves the existing token-local round-trip proof. A
contextual lexer would make its universal punctuator lemma false: a printed
division token followed by a space and `a /` would become a regular
expression at an expression-start state. Adding the preceding token is not
enough: a closing parenthesis can end either an expression or an `if`
condition. Supporting the unrestricted spelling needs a grammar-sensitive
lexical invariant, rather than weakening the round-trip theorem.

The literal reader proves its consumed prefix and replay with an arbitrary
suffix. These lemmas extend `lexKind_text`, `lexKind_ok` and the parser's
`parseChars_reads` theorem. Tests compare literals after an `if` condition,
division, empty classes, Unicode characters and escaped slashes with `tsc`.
Tokens and expression trees keep the target edition: the interpreter must
not lose the ES2015 meaning of `\s` when it receives the parsed tree.

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

The matcher in `Spec/RegExp.lean` uses that measure for a total repetition
helper and structural recursion on patterns for compilation. The helper
guards against a candidate that moves backwards, so its measure decreases
even for an arbitrary atom function. `compile_forward` proves that compiled
atoms call their continuations only at positions at or after their start.
`repeat_spec_step` then proves that the extra guard has no effect on such
atoms. Each compiled atom and continuation is already a total Lean function,
so the composition needs no fuel bound.

This model permits exponential backtracking. It makes no claim of linear
running time, and a real engine may run out of resources. There is no model
fuel whose exhaustion could be mistaken for `false`, `null` or an unchanged
string. The first implementation therefore does not need the conditional
fuel fallback considered for recursion.

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
