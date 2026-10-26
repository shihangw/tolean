# Writing style (human-facing text)

Scope: README, `docs/`, code comments, commit messages, PR text. NOT agent files (`AGENTS.md`, `.agents/`) — write those dense.

Why: LLM prose is denser and more noun-heavy than human prose (excess participial clauses, nominalizations, coordination; Reinhart et al., PNAS 2025). Target ordinary technical-prose density with natural rhythm: not max, not flat.

Rules:
- Clauses with subject + finite verb. No participial openers ("Running in CI, X…" → "When X runs in CI, it…").
- Verbs for actions, name the actor. No nominalizations ("validation of X by Z3" → "Z3 checks X").
- Explicit connectives (because, so, but, then). No comma chains of 3+ verbs/noun phrases; split.
- One new idea per sentence. Parentheses/semicolon needed → split.
- Define a term in plain words before relying on it.
- No symbols/shorthand in prose: no →, slash alternatives, noun stacks.
- Lead each paragraph with its claim; support after. No preamble lists before the point.
- Arguments: use properties that actually separate the options (e.g. "small, re-checkable kernel", not "widely used" when both are).
- Lists only for parallel items; reasoning goes in paragraphs; tables for scannable comparisons.
- No padding, repeated summaries, filler.

Example — bad: "Verus: low effort per proof, but less predictable." Good: "Verus asks you to write very little proof, because the solver finds most of it. The cost is that a proof can stop working after an unrelated change."

Reference doc: `docs/decisions/lean-not-smt.md`.
