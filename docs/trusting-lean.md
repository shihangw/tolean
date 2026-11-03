# What Tolean trusts in Lean itself

Every link in the README's [table of links](../README.md#what-is-proved-and-what-is-trusted)
also relies on parts of Lean. Most of them are trusted by every Lean proof,
but they are trusted all the same, so this page lists them. A certified file trusts fewer of them, because the kernel runs the
parser and the translator again inside the certificate.

A part is trusted when nothing would notice its mistake: a false theorem
would look proved, or Tolean would report the wrong thing. A part is checked
by the kernel when the kernel checks everything that the part gives it, so a
mistake shows up instead of passing. At worst, a true theorem fails to check,
or a certificate fails. Neither word means proved correct. Nothing in Lean is
proved correct, not even the kernel.

| Part of Lean | What Tolean uses it for | A certified file | Other files |
|---|---|---|---|
| The kernel | It checks every theorem. In a certificate, `decide +kernel` also runs the parser and the translator. The kernel computes with `Nat` literals through GMP and reads string literals itself, and both are part of it. | Trusted | Trusted |
| The axioms | Each claim lists the axioms its proof may use, such as `propext` and `Quot.sound`, and `tolean chain check` fails when the proof uses another. `native_decide` and `bv_decide` add axioms that trust compiled code, so a proof that uses them fails the check. | Trusted | Trusted |
| The elaborator and tactics, for proofs | They build the terms that the kernel checks. | Checked by the kernel, which refuses a wrong term | Checked by the kernel, which refuses a wrong term |
| The elaborator, for claims | It turns the text of a `Spec` file, which people read, into the statement that the kernel checks. When a notation or a coercion means something other than what the text seems to say, the theorem is not the one that people read. | Trusted | Trusted |
| The compiler and runtime | They run the `tolean` binary, and so the parser and the translator. Some functions of Lean's library, such as those on `String`, `Array` and `Nat`, run as C code (`@[extern]`) in the binary, and the kernel uses their Lean definitions instead. | Checked by the kernel, which runs the parser and the translator again | Trusted |
| `Lean.Json`, which is built on `Std.Internal.Parsec` | It reads `tolean.json`, the `--config` option, the chain manifests, and the programs that `interpreter.test.ts` gives the interpreter. A wrong reading can change which files are translated, with which settings, and what `chain check` and `chain trust` report. It cannot change what the kernel accepts. | Trusted | Trusted |
| `Float` | `instance : JSNumber Float` in `tolean/TypeScript/Interpret.lean` runs the interpreter on C doubles, so the test of the interpreter against Node relies on it. | Trusted | Trusted |
| Lake | `lake build --wfail` checks each module with the kernel when it compiles the module. A module that imports it reads its `.olean` file without checking it again. | Trusted | Trusted |
| The toolchain | `lean-toolchain` pins Lean 4.30.0 for elan, and `flake.nix` pins a `nixpkgs` commit with the same version for CI. | Trusted | Trusted |

CI checks the build again with `leanchecker`, which ships with Lean. It sends
each declaration of the built `.olean` files back to the kernel. A
declaration can reach an `.olean` file without the kernel: with
`set_option debug.skipKernelTC true`, or through a command that adds it with
the check off. The build then passes, and the theorem lists no axioms, so
`chain check` passes too. `leanchecker` refuses it, and it also refuses a
stale or altered `.olean` file. `leanchecker` uses the same kernel, so it does
not check the kernel itself. Independent kernels exist, such as
[Lean4Lean](https://arxiv.org/abs/2403.14064), which is written in Lean and
can check all of Mathlib. Running one in CI is a later step.
