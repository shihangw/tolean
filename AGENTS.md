# Agent instructions for Tolean

- Human-facing text: load the `writing-style` skill (`.agents/skills/writing-style/SKILL.md`); its description gives the scope.
- No session links (`claude.ai/code/session…`, `Claude-Session:`) in commits or PR text.
- New decision record: `docs/decisions/YYYY-MM-DD-<slug>.md`, dated when decided; the docs build enforces the prefix.
- Lean proofs about the parser (do-blocks, loops, fuel, the round trip): load the `proof` skill (`.agents/skills/proof/SKILL.md`).
