# Translate Go's `switch` as a chain of `if` statements

**Status:** accepted · **Date:** 2026-11-26

The proved Go translator writes an expression switch as a chain of `if`
statements, and an `if` with an init statement as a block that holds the
init statement and a plain `if`. The interpreter keeps its own rules for both
statements, written from the Go specification's sections "Switch statements"
and "If statements". `tolean/Go/Proof/Switch.lean` proves that the
interpreter gives each statement and its rewritten form the same outcome in
every environment, so the existing statement proof covers the rewritten form.

## The tag is evaluated in every test

Go evaluates the tag of a switch once. The chain evaluates it again in each
case test, as `x == a || x == b`, and the translator binds no name for it.
The repeated evaluation changes nothing, because the interpreter is a
function of the environment and expressions of the subset have no effects. A
call evaluates to the same value each time.

The one difference is a tag that has no value, such as a call that runs out
of fuel. The switch then has no outcome. The chain has none either, provided
that it evaluates the tag at all, which its first case test does. A switch
with a tag and no case value would run its `default` clause without
evaluating the tag, so the translator refuses it. Go programs rarely write
one.

Binding the tag to a fresh local would avoid the repeated work, but the
proof relates the interpreter's environment to the output's name by name. A
local that the source does not have would break that relation for the rest
of the function.

A panic works the same way. When the tag divides by zero, the switch
panics, and so does the first case test. The translator refuses a division
in the right operand of `||`, so a clause with several values may not divide
in its later values, and the tag may not divide when such a clause exists.

## Scope of an init statement

The name that an init statement declares goes out of scope at the end of the
`if` or `switch`. When neither branch returns, the translator writes the
block with `letState`, which copies back only the locals declared outside the
block, as it does for the branches of an `if`. The init statement's name does
not reach the code after it.

When a branch returns, the existing translation puts the code after an `if`
into its `else` branch. With an init statement, that code would run where the
init statement's name is still bound in the output and no longer bound in the
interpreter. The statement proof requires the two environments to agree on
every name, so the translator refuses this form unless the statement is the
last one of its list. A later change can lift the restriction with a lemma
that an output body ignores names outside the translator's scope.

## `break` in a switch

Go's `Outcome` now has `brk` and `cont`, as the shared loop core requires.
A `break` in a switch ends the switch, and the switch then ends normally, as
the Go specification's section "Break statements" says. The interpreter maps
the `brk` of the chosen clause to a normal outcome. `Switch.lean` proves that
the chain of `if` statements gives the same outcome after this mapping.

The translator writes a switch whose clauses break as its own body, which
ends with the locals that the switch changes. A `break` in a clause returns
those locals at once, and the rest of the clause is skipped. The code after
the switch then reads them. A switch that changes no local has nothing to
return, so the translator refuses it. A switch with an init statement becomes
a block, so the init name does not reach the code after the switch.

A `continue` inside such a switch would have to leave both the switch and the
loop's body. The translator refuses a switch that both breaks and continues,
because the body of the switch cannot say which of the two it ends with. A
switch that only continues still works, since its `continue` reaches the loop
unchanged.
