# Plan: print the Tolean IR with Lean's own printers

**Status:** planned, not built · **Date:** 2026-11-03

The printer in `tolean/TypeScript/IR.lean` writes the [Tolean
IR](../decisions/2026-10-30-tolean-ir.md) as Lean text by hand. It chooses
every word and every line break itself. Two parts of Lean could take over
some of that work, and code that Lean supports officially, and that every
Lean user runs, deserves more trust than a printer of our own. This plan
moves the layout to `Std.Format` first, and then tries `Lean.Syntax`.

Neither step removes the printer link. The link is about meaning: the
printed Lean must compute what the IR computes. A certificate proves that for
its file, whichever printer wrote the text. So both steps make printing bugs
rarer, but a file without a certificate still trusts the link.

## Step 1: lay the text out with `Std.Format`

`Std.Format` is Lean's layout engine. A printer builds a document out of
text, line breaks that may become spaces, and groups, and `Std.Format`
chooses where to break each line. It is a pure function in `Init`. It needs
no environment, so it runs in the `tolean` binary and in the WebAssembly
build alike.

The printer keeps choosing the words, and it hands the line breaks to Lean.
Our code then decides less about how the output looks, and the part that it
still decides is easier to read.

## Step 2: try writing the text with `Lean.Syntax`

Here the printer builds a `Lean.Syntax` tree, and Lean's formatter writes
the text. Text that Lean's formatter writes from a syntax tree is text that
Lean's parser reads back as that tree, so the printer could no longer write
text that Lean parses in another way than it meant. On Lean 4.30, building
the tree is pure, but formatting it is not. Three findings decide whether the
step works:

- **It needs Lean's environment.** In an empty environment, `ppCommand`
  fails with "Unknown constant `termIfThenElse`". So the `tolean` binary
  would load Lean's `Init` when it runs. Users of the binary have a Lean
  toolchain, which has it. The playground already runs Lean in the browser,
  so it may have it too.
- **Names need care.** A quotation marks its names for hygiene, and the
  formatter prints the marks, as in `raise✝`. `Unhygienic.run` leaves them
  too, so the printer must make each name with `mkIdent`.
- **The output changes.** Lean's formatter chooses its own line breaks, so
  every golden file of the corpus would change once. The output must stay as
  easy to read as it is now.

## How each step is checked

Each step first prints every corpus file both ways, behind a flag. It is done
when these hold:

- every certificate still passes;
- the WebAssembly build still runs, and still gives the same Lean as the
  native command;
- a person has read the new golden files, which change once, and finds them
  as easy to read as before.
