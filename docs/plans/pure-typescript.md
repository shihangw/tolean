# Plan: translate the pure TypeScript that real modules use

**Status:** in progress · **Date:** 2026-11-03

Pure TypeScript in practice uses much more of the language than the subset
accepts. A function is pure when it does no input or output and depends only
on its arguments. A survey of one pure module of about 2,000 lines, which
folds a list of events into a state, found generics, recursion, callbacks,
closures, exceptions, `Map`, `switch` and template literals in almost every
file. When the survey ran, Tolean could translate none of its fourteen files.
What Tolean translates now is in the [TypeScript
guide](../typescript/README.md).

This plan lists what is left to add so that such a module translates
without a rewrite. It also states the rules that each addition must keep,
and the behavior that Tolean must still refuse.

## The rules for every addition

Every new construct keeps three rules. A construct that cannot keep them
stays refused, even when the code that uses it is pure.

1. **ECMA-262 specifies the behavior, and it is deterministic.** The spec
   must define the result, and the result must be the same in every edition
   that a target allows. Each construct records the edition that added it and
   the section that defines it, in `tolean/TypeScript/Edition.lean`. The
   section numbers in this plan are those of ES2024. Behavior
   that the spec leaves to the engine, the locale or the time zone stays
   refused.
2. **The translation sees every change to state.** The translation is a
   shallow embedding, so a Lean value cannot change behind a name. A `Date`
   and a class instance are references in JavaScript, so two names can point
   to one object. Each of them gets the ownership rule that arrays, maps and
   sets have now: only the function that created the object may change it,
   and nothing else may hold it while it changes.
   Interface fields need not say `readonly`, because the translator refuses
   every field write regardless of that mark. The [TypeScript
   guide](../typescript/README.md#the-subset) explains why the claim concerns
   each call's values, not aliases that caller code keeps between calls.
3. **The proof of the translator still covers it.** Each construct extends
   the Tolean IR, its evaluator and the interpreter, so `program_sound` holds
   for programs that use it. `tests/typescript/interpreter.test.ts` checks
   the interpreter against Node on random programs that use it. Both
   translators give the same output, byte for byte.

## What to add

The tables group the constructs by the stage that adds them. Each row says
what the Lean output is, and what Tolean refuses so that the translation stays
exact. A construct leaves these tables when Tolean translates it, and the
[TypeScript guide](../typescript/README.md) documents it from then on.

### Types and narrowing

Inline object types now use generated structures. This includes object
aliases and anonymous members of named tagged unions. The translator shares
equivalent shapes and captures their lexical type parameters rather than
giving each annotation a different nominal type. The
[TypeScript guide](../typescript/README.md#the-subset) describes the supported
positions and the restrictions inherited from named interfaces.

| TypeScript | Lean | Refused |
|---|---|---|
| `f?.()` | No accepted program to translate: `Syntax.TypeExpr` and `Translate.Ty` have no function type, and no accepted declaration gives a possibly `undefined` value a callable type. A generic type parameter does not make a value callable. Local function values cannot escape a direct call. | Optional calls stay refused; so does `==` against anything except `null` and `undefined`. |

[#247](https://github.com/shihangw/tolean/pull/247) fixes optional indexing
after a conditional join makes a `Record` nullable, as in
`(absent ? null : r)?.[k]`. The required-certificate fixture and
Node-backed interpreter test cover that case. Optional calls remain refused.

### Functions

| TypeScript | Lean | Refused |
|---|---|---|
| An arrow function passed to a function of the program, which reads only `const` values and parameters | `fun` | A callback that changes a variable outside itself |
| A state-writing local function whose final return is an expression or names a variable other than a changed captured variable | A Lean function that returns the value and the new values of the captured variables, which the call binds again | A `return` before the last statement of such a function |
| A sibling call whose callee captures variables not named by the caller, a longer chain of sibling calls, or a value-returning caller that changes state only through sibling calls | Lifted functions with transitive capture and state arguments | Recursive local functions |
| A function-typed field or parameter, such as a comparator in an options object | A field of a function type | A function value that changes state when it is called |
| A destructured parameter, such as `{ a, b }: Options` | A pattern on the structure | Defaults inside the pattern |
| A default parameter value | `Option` with a default at the call | A default that reads another parameter |
| `while` and `do … while`, with a `@decreases` tag that names a measure | A recursive function with `termination_by`, as for recursion below | A loop without such a measure |
| A rest parameter `...xs: T[]`, and a spread argument `f(...xs)` | A `List T` argument | A spread argument to a function whose parameters are not a rest parameter |

### Generics

| TypeScript | Lean | Refused |
|---|---|---|
| A type parameter with a constraint, such as `T extends Named` | Nothing in the first version | All constraints, until the open question below is settled |

A constraint is hard to translate, because TypeScript checks it by the shape
of a type and Lean has no subtyping by shape.

### Recursion

| TypeScript | Lean | Refused |
|---|---|---|
| Recursion where a call does not pass a part of one parameter, with a `@decreases` JSDoc tag that names a measure | A `def` with `termination_by` that measure. Lean must prove that each call makes the measure smaller, and the translator refuses the file when Lean cannot. | Recursion without such a proof |
| Functions in one file that call each other | A `mutual` block | Recursion across files |
| A tagged union whose members refer to the union, such as `interface Add { readonly kind: 'add'; readonly left: Expr }` with `type Expr = Num \| Add` | A `mutual` block of the structures and the inductive type, which Lean accepts | |

Lean also accepts `partial def` without a proof that the function ends. But
Lean cannot prove anything about a partial function, so Tolean never writes
one. A JavaScript call can also fail where the Lean function does not: deep
recursion makes Node throw a `RangeError` when the stack runs out. So a claim
about a recursive function holds when the JavaScript call returns, as every
value claim already does.

### Arrays

| TypeScript | Lean | Refused |
|---|---|---|
| The `index` argument of a callback other than one of `map`, and the `array` argument of any callback | The `List` functions that also pass the index, as `List.mapIdx` does for `map`, and the list itself | |
| A number-sort certificate inside a callback other than `map` or `filter`, for changing loop state or body-local lists, for a remaining computed list shape, or under an enclosing nullable narrowing | A hypothesis over the parameters excludes `NaN` keys, or requires finite keys for a difference. Sorts and calls in ordinary expressions and records, in `map` and `filter`, and over loop elements or captured inputs already carry these conditions. Inputs may use parameter fields, local aliases, spreads, literal elements, maps, filters, slices, conditionals and calls. Calls in nullable matches carry guarded conditions for the selected branch. | Lists that cannot be reached from parameters. |

The certifier uses `sortValues_sortWith_on` for a direct sort of a
parameter. Its input hypothesis excludes NaN keys for a comparison, or
requires finite keys for a difference.

### Strings

Each operation below becomes a function on `JSString`, the list of UTF-16
code units that Tolean translates a `string` to, written from its algorithm
in the spec. [A decision record](../decisions/2026-11-06-jsstring.md)
explains the model.

A literal that holds a lone surrogate, such as `"\uD800"`, should print its
code units. The lexer refuses it now, because the syntax tree keeps the text
of a literal as a Lean `String`.

| TypeScript | Lean | Refused |
|---|---|---|
| A number argument of `padStart` or `padEnd` that is not an integer literal | `ToLength` on the argument, then padding on code units. A dynamic length can exceed the engine's string limit and throw a `RangeError`, whose opaque message the error model does not yet support. | |

Issue [#218](https://github.com/shihangw/tolean/issues/218) is partly
implemented. PR #239 delivers flagless regular-expression `test` with a
string argument. `test` accepts a literal or an alias to one. A literal must
start with `(?:` so the parser can distinguish it from division. The matcher
uses UTF-16 code units and total ordered backtracking.

PR #244 adds first-match replacement, including empty matches, only for
`s.replace(/(?:pattern)/, "replacement")`. The pattern may contain captures,
but the replacement must be a literal without `$`; captures affect matching
but are not substituted into the result. Replacement requires a direct regex
literal, while `test` may use an alias. Dynamic replacement strings remain
refused because they may contain substitution tokens. Dollar substitutions
and function replacers remain refused because their semantics are not modeled.
Flags `i`, `g`, `m`, `s`, `u`, `y`, `d` and `v` remain refused. Global and
sticky searches need `lastIndex` state, while the other flags change pattern
or matcher semantics.

The parser refuses ordinary `/pattern/` literals and regular-expression
constructor calls. The supported grammar includes capturing and
non-capturing groups, but refuses lazy quantifiers, backreferences,
lookaround, named groups and escapes without a specified character set.

`String.match` and `RegExp.exec` remain refused because their results need a
representation for `null`, unmatched captures as `undefined`, and the
`index`, `input` and `groups` properties. The interpreter, IR evaluator and
`program_sound` proof do not yet cover that result shape. Regex values also
remain outside certificate boundaries because certificates have no encoder
or decoder for them. The [decision record](../decisions/2026-11-14-regexp-subset.md)
explains these restrictions and the future work.

### Maps and sets

| TypeScript | Lean | Refused |
|---|---|---|
| A map borrow with an early return, an ordinary returned value, control flow or an imported callee | A function that returns the changed maps, with its ordinary result when there is one. The caller binds the changed maps again. | A call where the caller keeps another name for the same map |

The translator now accepts one changed Map parameter in a void function
whose body contains only straight-line set, delete and forwarding calls
with atomic arguments and an optional terminal bare return. The body may
also call a function that throws, and the throw passes on to the caller.
The call copies the map in and back out, and `program_sound`
covers that call rule. The [TypeScript guide](../typescript/README.md#map-borrows)
describes this case. The remaining cases need a wider call result, including
the final parameter bindings when the callee returns or throws.

The initial value of a `reduce` can read a map or a set that `new Map(items)`
or `new Set(items)` makes from a list it cannot see, such as a parameter:
`xs.reduce((a, x) => a || x, new Set<bigint>(ys).has(0n))`. The link proof
unfolds the constructor only on a visible list, so the set would stay
`Eval.setOfItems` of an unknown list. The certifier therefore refuses such an
initial value. A lemma about `setOfItems` and `mapOfItems` would let it
write the certificate.

### Numbers and dates

| TypeScript | Lean | Refused |
|---|---|---|
| `**` on `bigint` (§6.1.6.2.3) whose exponent is not a literal | `a ^ b.toNat`, after a check that `b` is not negative. JS throws a `RangeError` otherwise, so this needs a built-in error whose message the program cannot read. | `>>>` on a `bigint`, because it throws |
| `BigInt(n)` (§21.2.1.1) | A conversion that throws a `RangeError` when `n` is not an integer. Its message is up to the engine, so this needs a built-in error whose message the program cannot read. | |
| `d.toISOString()` | The Date Time String Format of `JSDate`. It throws a `RangeError` for an invalid date, so this needs a built-in error whose message the program cannot read. | Local-time getters, setters, and `Date.now()` |

`Except` and per-file error classes already exist, but their errors carry
specified messages. They do not model the opaque message of a built-in
`RangeError`. The new number laws are hypotheses, as the
current ones are. `jsNumberLaws.test.ts` checks each of them on every
maintained Node release line.

## What stays refused

These stay refused after the plan is done, because no translation of them can
be exact:

- `localeCompare`, `Intl`, and every local-time `Date` method, because their
  results depend on the host.
- `normalize`, and `toUpperCase` and `toLowerCase` on a string that the
  translator cannot show is ASCII, because their results follow the Unicode
  version of the engine, and that version changes between Node releases.
- `Date.now()`, `Math.random()` and `crypto`, because they are not
  deterministic. The [effects plan](effects.md) makes them inputs.
- `Error.prototype.stack`, and every other property that ECMA-262 does not
  define.
- `toLocaleString` and the other `toLocale…` methods, and `Number.prototype.toFixed`
  and its relatives until the model of `Number::toString` covers fractions.
- `structuredClone`, `setTimeout` and the other functions that the host
  provides, because ECMA-262 does not define them.
- `Symbol`, `Proxy`, `Reflect`, `eval`, `with`, `arguments`, and getters on
  object literals.
- Assignment to an array's `length`, `delete` on objects, and `Object.assign`
  onto an object that the function does not own.
- `Object.keys`, `Object.entries` and `for … in` on objects with keys that look
  like integers. ECMA-262 lists those keys first, in numeric order
  (§10.1.11.1), so the order differs from the order of the literal. These
  are accepted on objects whose keys the type fixes and none of which looks
  like an integer.

## Unfinished parser work

[#208](https://github.com/shihangw/tolean/issues/208) remains open, but merged
[#217](https://github.com/shihangw/tolean/pull/217) accepts its original
example, `a < b && c > d`. A CLI translation of a typed
`between` function containing that exact return expression succeeds. The
issue still needs a broader fix: a typed function calling
`f(a < b, c > d)` is refused, although TypeScript 6.0.3 reads two comparisons
there. This is a known gap, not a permanent restriction, so the case is not
in the rejection corpus.

The parser accepts comparisons when a top-level `&&`, `||`, `??`, `===`,
`!==`, `==`, `!=`, `+`, `*`, `/`, `%` or `**` rules out a type list before a
closing `>`. The scan keeps going inside brackets, because a type literal can
contain a computed property name. It also keeps going at `-`, `&`, `|`, `.`,
`!` and `?`, because types can contain them. The conservative treatment of
`>>`, `>=`, `<<` and `<=` remains unchanged because TypeScript rescans `>`
while it closes type arguments. The unrelated merged
[#230](https://github.com/shihangw/tolean/pull/230) fixes WebAssembly list
termination and does not change this parser rule.

Merged [PR #242](https://github.com/shihangw/tolean/pull/242) prepares the
proof interface for a later ambiguity check; it does not change which source
expressions the parser accepts. Its token observations retain token kinds
(including identifier text), preceding line breaks and adjacency across
fragment boundaries. Its prefix and suffix relations let a future probe be
reasoned about in surrounding token contexts and across printed suffixes.
The current parser still scans token kinds and still refuses
`f(a < b, c > d)`.

The remaining task is to parse a possible comma-separated type list
speculatively, then apply TypeScript 6.0.3's follow-token test. In
`f(a < b, c > d)`, `b, c` can parse as types, but the following `d` can start
an expression, so TypeScript reads two comparisons. In
`f(a < b, c > (d))`, the parenthesis can instead follow type arguments, so
TypeScript reads a call with type arguments; `f < A, B > (x)` is the same
kind of ambiguity. The future check must use the token adjacency and
line-break information that its rules inspect, and the round-trip proof must
show that printing preserves the probe's decision. Until that work is done,
the parser should keep refusing the type-argument cases and any form whose
reading it cannot establish. Extending the operator stop set alone does not
complete #208.

## Steps

Each step ends with all checks green, with both translators in agreement, and
with no change to the output of code that is already in the subset. A fix
for output that Lean does not accept may change that output too.

Each step has a priority. The P0 steps come first, then the P1 steps, then
the P2 steps. Steps with the same priority keep the order of their numbers.
The steps keep the numbers that pull requests refer to, so a finished step
leaves a gap.

8. **P0.** Widen map borrows to early returns, an ordinary returned value,
   control flow and imported callees. Several changed maps and a throw out
   of a called function are done.
10. **P1.** Sorting: number-key certificates inside the remaining callbacks, for changing loop state and body locals,
    remaining computed list shapes, and direct sorts or conditioned helpers
    under enclosing nullable narrowing. Calls inside nullable matches are
    covered.
11. **P2.** Recursion: the translator accepts self-referential interfaces and
    single-function structural recursion when Lean accepts their declarations
    and proves the function terminates. Certificates for recursive interfaces
    and functions remain refused. A recursive interface needs a reusable
    nested encoder and decoder round-trip proof; a recursive function needs
    existential fuel and a proof that additional fuel preserves successful
    interpreter results. Recursive tagged
    unions remain refused because the translator does not emit their member
    interfaces and union as one mutual type block. User-supplied `@decreases`
    measures, mutual recursion and `while` loops also remain refused because
    the translator has no checked termination obligation for them. See the
    [decision record](../decisions/2026-11-17-recursion-certificates.md).
12. **P1.** Non-literal `bigint` exponents, `BigInt(number)`,
    `toISOString`, and non-literal padding lengths. These still need a
    model of built-in errors whose messages the program cannot read.
13. **P2.** Readonly ordinary classes elaborate to interfaces, object
    constructors and free method functions before interpretation and
    translation. Dispatch requires exactly one statically known class type.
    The parser round trip is proved, and Node comparisons test elaboration.
    A proof that elaboration preserves the original JavaScript semantics
    remains open. Constructor identity, `instanceof`, escaping `this`,
    inheritance, accessors and mutable fields remain refused.
    The [decision record](../decisions/2026-11-17-readonly-classes.md) distinguishes
    these proof boundaries. The existing `extends Error` subset is separate.
14. **P1.** Local functions: general final return expressions in functions
    that change captured variables, implicit transitive captures, longer
    sibling call chains, and value-returning callers with only indirect state changes.
17. **P2.** `try` and `catch`: accept `try { … } catch (e) { … }` where the
    catch tests `e` with `instanceof` or ignores it. Keep `finally`, rethrowing
    a changed value and throwing anything but an error refused. See the
    [`try` and `catch` open question](#open-questions).
    The [initial scope](../decisions/2026-11-17-try-catch.md) refuses try
    bodies that change outer state and built-in operations whose errors
    are not modeled. Mutable try bodies need environments on thrown
    completions. The first slice handles terminal try statements whose
    handlers ignore the binding. Protected bodies allow local initializers,
    branches and explicit built-in Error throws over simple expressions.
    All calls, other potentially throwing operations and nested protected
    try statements remain refused until their effects are analyzed.
    Caught-value tests and rethrows need a typed caught value. These parts
    of step 17 remain open.
18. **P2.** Proof obligations: Tolean states `Consistent cmp` for a comparator
    outside the two known shapes and accepts a project-supplied proof beside
    the output. The build checks the proof for `sorry` and axioms. The same
    mechanism later serves `@decreases`. See the
    [proof-obligation open question](#open-questions).
    The first slice adds project manifest obligations with exact theorem
    types and a fixed axiom policy. Its chain tests cover obligations'
    fixed axiom policy, not claim-specific axiom allowlists.
    The next slice generates consistency
    statements for additional bigint comparators and passes project proofs
    through the sort link theorem. Generated output determines the required
    obligations. Other element types, captures of generic types and
    `@decreases` obligations remain refused. See the
    [decision](../decisions/2026-11-17-project-proof-obligations.md).

Step 8 matters most for proofs, because a fold over events keeps much of its
state in maps.

## Refactors from review

These entries record design feedback from pull requests and separate fixes
that have landed from work that remains. A fix in a descendant does not mean
that the earlier pull request already contains it.

- **Make expression scans exhaustive.** Enumerate leaf constructors instead
  of ending a scan with `| _ => false` or `| _ => []`. Traverse ordinary
  children, and name any deliberately unsupported binding scopes explicitly.
  Audit the call, name, callback and number scans rather than adding another
  independently maintained partial traversal. Keep source-call counts as
  invariant checks, not as the definition of which syntax is supported.

  The [call-traversal review on #220](https://github.com/shihangw/tolean/pull/220#discussion_r4576745761)
  identified dropped `.struct` fields and `.structUpdate` children.
  **#220 now covers the condition-call traversal:** `conditionCalls` visits
  record fields, the update base and replacement fields, and enumerates
  leaves explicitly. The source scan also counts calls in object spreads.
  Required certificates cover each record position and both update sides.
  `bodyConditionCalls` explicitly refuses tagged narrowing with a named
  scope error because its rebound parameter needs guarded conditions over
  the original union. #238 retains its additional record certificate cases.
  The other scans still need the broader audit described above.

  The [number-use scan on #221](https://github.com/shihangw/tolean/pull/221#discussion_r4576744315)
  has landed: `exprUsesNumber` follows an optional-index receiver, and it
  names the expression forms that cannot use numbers. The accepted
  `optionalIndexNumberReceiver` fixture keeps the receiver-only regression
  visible. Do not repeat that fix. The broader scan audit remains open,
  because `typeUsesNumber` and `stmtUsesNumber` still have fallback cases.
  Keep checking all of these traversals against their syntax constructors;
  do not treat source-call counts as a definition of coverage.

- **Preserve the state-aware local-function return path.**
  The [review on #226](https://github.com/shihangw/tolean/pull/226#discussion_r4576809523),
  also inherited by #236, found that `callLocal` could run a state-writing,
  value-returning body twice. That is fixed: `callLocal` recognizes a
  changing body with a final value return before it calls `execStmt`, then
  runs `execReturnState` once and writes the captured values back. This fixes
  execution order, not the supported syntax. Earlier returns with captured
  changes still have no modeled result. Step 14 still tracks general final
  return expressions, transitive captures, longer sibling call chains and
  callers whose local functions change state only indirectly.

- **Preserve both map-escape regression tests.**
  The [review on #231](https://github.com/shihangw/tolean/pull/231#discussion_r4577273721)
  found that a rebase removed the nested-map case where `forward(a, b)`
  stores `b` in `a` through `change`, then the caller mutates `b`.
  [#231](https://github.com/shihangw/tolean/pull/231) restored that test in
  commit `4bd0eac`, with `refused: true`, alongside the direct-call escape
  test. Keep both tests so the direct and forwarding paths stay protected.

- **Share literal-encoding normalization between certificate proof paths.**
  The [review on #233](https://github.com/shihangw/tolean/pull/233#discussion_r4576995912)
  found that a literal appended inside a conditional callback prevented the
  sort lemma from matching. #237 fixes the concrete certificate failure,
  as the reviewer verified, but the step 10 tip still emits the reverse
  literal-map and append normalization in separate callback, loop and
  function paths. Extract one proof-emission step that takes the required
  encoders. Keep the nested literal-append and loop certificate cases so
  the shared step preserves their normalization order.

- **Complete the structural type-argument ambiguity check.**
  The merged [#217](https://github.com/shihangw/tolean/pull/217) validates
  the bounded operator stop set, not a complete ambiguity algorithm. Merged
  [#242](https://github.com/shihangw/tolean/pull/242) supplies observations
  and prefix proofs for a later probe, but does not implement that probe.
  Retain #217's bracket-depth rule and pinned-TypeScript controls. The
  remaining work is the speculative type-list parse, TypeScript's
  follow-token test, and a round-trip proof that preserves the identifiers,
  contextual tokens, adjacency and line breaks those checks use.

## Open questions

An open question ends with a recommendation until a step decides it. A
decision record then states the choice and any limits that remain.

- How should a certificate cover a generic function or interface? Before the
  generic codecs, the certifier had no encoder for a type parameter, so a file
  with either got no certificate. The claim could take an encoder for each
  type parameter as an argument, since the code never looks inside such a value.

  Decision: require a `Codec N T` for each type parameter. A codec proves that
  its decoder reverses its encoder, and that the encoder never gives `null`
  or `undefined`. The exclusions distinguish a payload from the nullish case
  of a surrounding type, which lifts the optional-nullable generic refusal.
  A generic interface gets a codec constructor from the codecs of its
  parameters. Recursive interfaces and generic-interface uses with a
  non-parameter argument remain refused; see the
  [decision record](../decisions/2026-11-16-generic-codecs.md).

  Separate loops over `bigint | undefined` and loops that capture a generic
  nullable value certify, including when a function contains several loops.
  Returning loops certify when they change one or two locals and when their
  elements are optional or nullable. A returning loop followed by one plain
  loop also certifies.

  `nestedLoops<T>` certifies when its outer loop narrows an element of
  `ReadonlyArray<bigint | undefined>` and adds it to an accumulator, then its
  inner loop adds bigint elements when a captured `T | null` value is null.
  Two returning loops over `bigint | undefined` or `bigint | null` also
  certify. Each loop exposes a shared returned-or-completed result, which
  the proof splits before it continues to the next loop.

  An outer `bigint | undefined` loop with two inner loops around an
  accumulator update now certifies too. The certifier applies each child
  lemma to the environment at that point, after the preceding fold and
  accumulator update. Required fixtures also cover three returning loops
  with mixed element types and two returning loops that share an accumulator.

  An inner loop that returns from the function is refused during translation
  for every element kind in the matrix, whether the outer loop contains one,
  two or three inner loops. The refusal says that a loop body may return only
  where the statements after the loop end in a return. This translation
  restriction remains separate from the certificate composition fixed in #289.

- How should a certificate cover an interface that refers to itself, and a
  function that calls itself? The decision is to keep both outside certificates
  until the recursive codec and fuel proofs exist. The certifier refuses them
  with explicit errors. The
  [decision record](../decisions/2026-11-17-recursion-certificates.md) gives
  the reasons and limits. For a later implementation, quantify the fuel
  existentially for each input:

  ```lean
  theorem f_cert (x : Tree) : ∃ n, ∀ fuel, n ≤ fuel →
      run program "f" [encTree x] fuel = some (encTree (f x))
  ```

  The proof follows the function's own `termination_by`: induction on
  `sizeOf x`, where the step takes the largest of the children's fuels. That
  step needs one lemma the library lacks, that more fuel never changes a
  `some` result of the interpreter or of the IR evaluator. The existential
  form composes: a caller of a recursive function gets a claim of the same
  shape. An explicit bound such as `sizeOf x + depth ≤ fuel` would leak into
  every caller's statement.

- How should a certificate cover a counted `for` loop? The interpreter gives
  no value when the counter would pass `Number.MAX_SAFE_INTEGER`, as it
  would for a bound of `Infinity`, so the claim that it gives a value for
  every input does not hold. The claim could take the hypothesis that the
  interpreter gives a value, or that the bound is at most
  `Number.MAX_SAFE_INTEGER`.

  Decision: take a hypothesis on the bound, stated over the parameters. The
  [decision record](../decisions/2026-11-16-counted-loop-certificates.md)
  records why the certificate requires this precondition and keeps non-parameter
  bounds refused.

  The translation of a counted loop is the `for … of` fold over
  `JSNumber.countUp k b`, the IR evaluator gives `countUp? k b` and has no
  value when that is `none`, and `countUp` is `countUp?` with `[]` for
  `none`. So the link theorem fails only where `countUp? k b = none`, and
  each counted loop adds one binder to the function's two theorems.

  Nullish narrowing guards stay around the bound's condition when it reaches
  the function boundary. Enclosing loops carry child safety conditions in
  their invariants, so their lemmas do not rely on a later function hypothesis.
  A non-nullable bound needs no guard:

  ```lean
  theorem sum_cert {N : Type} [JSNumber N] (xs : List Int) (n : N)
      (h0 : (JSNumber.countUp? 0 n).isSome) :
      run program "sum" [encList Val.int xs, Val.num n] = some (Val.int (sum xs n))
  ```

  The bound inside `countUp?` is the loop's bound, printed over the
  parameters as the translation prints it. For `i < xs.length` it is
  `JSNumber.ofSafeInt xs.length`, so the hypothesis says that the list has at
  most `Number.MAX_SAFE_INTEGER` elements. One library lemma,
  `countUp?_eq_of_isSome`, rewrites the evaluator's value into
  `some (.list (List.map Val.num (countUp k b)))`, which is the shape the loop
  lemma already proves, so the loop lemma needs no new code. The certifier
  checks that the bound reads only parameters and refuses the other loops. A
  literal bound such as `i < 10` keeps the hypothesis, because the theorems
  hold for an abstract number model and `countUp?` on a literal reduces only
  under the safe-integer laws. A follow-up can cover a bound that is a
  `const` local by inlining the chain of definitions back to the parameters.
  The other hypothesis, that the interpreter gives a value, would need the
  converse of soundness, that a value of the interpreter implies a value of
  the IR evaluator. That is a second proof of the translator and not worth
  its cost.

- How should a type parameter with a constraint translate? One option is a
  type class that the translator writes for each constraint, with one
  method per field that the constraint names. Another is to pass the
  fields that the function reads as explicit arguments.

  Recommendation: the type class. `T extends Named` becomes `[Named T]`, with
  `class Named (T : Type) where name : T → JSString`, and the translator
  writes `instance : Named Person := ⟨Person.name⟩` wherever it checks the
  constraint at a call. The signature then mirrors the TypeScript one, call
  sites stay as they are, `A & B` becomes two instance arguments, and a
  constraint on a generic interface's parameter works, which explicit fields
  cannot do. Explicit fields are dictionary passing by hand, and they change
  every caller. For a certificate, the codec of `T` gains one law per method:
  the object's field holds the encoding of the method's result. The first
  version accepts constraints that are interfaces or object types with
  typed fields, and refuses primitive bounds. Field writes stay refused,
  whether or not the fields say `readonly`. Every instance gets a name,
  so that instance search never has two candidates.

- Should `try` and `catch` come in a later step? The survey had none, but much
  other pure code catches its own errors.

  Decision: start with the [restricted catch scope](../decisions/2026-11-17-try-catch.md).
  `Except` alone does not preserve locals changed before a throw, so the
  first version refuses those changes. It takes `try { … } catch (e) { … }` where
  the catch tests `e` with `instanceof` or ignores it, and refuses `finally`,
  a rethrow of a changed value, and a `throw` of anything but an error. The
  locals that the `try` body assigns become its result tuple, as a loop
  body's do and a local function's do
  ([decision](../decisions/2026-11-12-local-functions.md)), but this threading
  covers normal completion only. Thrown completions need to carry the
  environment first.

- The map-borrow question is settled by the
  [decision to pass changed maps back](../decisions/2026-11-14-map-borrows.md).
  A single map now passes back on normal completion, including a terminal
  bare return and forwarding through another checked call. The remaining
  tuple result must carry several maps or an ordinary result as well.
  `ReadonlyMap` stays plain. Step 8 remains open because early returns
  and returned values still need to preserve the final parameter bindings.

- Should a comparator that is not one of the two shapes be accepted when the
  project supplies a proof that it is consistent?

  Decision: yes, with a fixed axiom policy and statements from Tolean.
  Tolean now generates these statements for `bigint` comparators that do not
  capture generic types. Other element types remain refused. The
  [project proof checks](../decisions/2026-11-17-project-proof-obligations.md)
  require the exact theorem type.
  Tolean states the obligation, `Consistent cmp`, as a theorem in the output.
  Its tactic proves the two known shapes. When the tactic fails, the project
  may supply the proof in a file beside the output, which the manifest
  records and the build checks for `sorry` and for axioms. The same
  mechanism could later cover a `@decreases` measure and keys that must not
  be `NaN`. Support for other comparator element types and captures of generic
  types also remains open. Counted-loop bounds already become certificate
  hypotheses, as described above. The statement always comes from Tolean and the
  project supplies only the proof, so a wrong proof fails the build and a
  wrong statement cannot get in. The obligation may restrict itself to the
  inputs, because a comparator on `number` keys is consistent only without
  `NaN`.

