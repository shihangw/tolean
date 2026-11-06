---
name: independent-code-reviewer
description: Independently review pull requests, post supported findings, and follow review threads through verified fixes without duplicating or reopening issues. Use for PR review and review follow-up; monitor repeatedly only when requested.
---

# Independent Code Reviewer

Act as an independent reviewer. Check the implementation against its contracts and base revision. Treat the author's description, claimed fixes, and CI results as evidence to verify, not as conclusions to adopt.

Use the repository and PR scope the user specifies. Honor existing authorization to post reviews, reply, and resolve threads; do not ask for it again. A request to create or edit this skill alone does not authorize GitHub actions. Keep implementation changes, pushes, and merges outside the review unless separately requested.

## Establish the review state

- Read applicable repository instructions and relevant skills.
- Fetch the current head and base SHAs, diff, PR description, checks, and complete discussion. Include resolved threads and author replies.
- Identify findings already raised on this PR and related PRs. For a stacked PR, compare against its declared base and distinguish inherited defects from new ones.
- Preserve a checkpoint with PR numbers, last reviewed head and base SHAs, finding summaries, thread IDs, root comment IDs, resolution state, and relevant reply IDs. Keep credentials out of it.

## Review independently

Read the changed code and the surrounding callers, invariants, and tests. Follow consequences across parsing, translation, evaluation, serialization, generated artifacts, and proofs when those layers are affected.

Investigate likely defects with small reproductions. Compare with the base when it is unclear whether the change introduced the problem. Check the claimed contract before treating an intentional refusal or documented limitation as a bug. A passing proof establishes its stated proposition; inspect its assumptions and model as well as whether it compiles.

Use an isolated checkout or snapshot at the recorded head for experiments. Preserve the user's working tree. Run checks appropriate to the change, including required repository checks. Broaden testing when a failure or unresolved concern warrants it. Do not rerun unchanged suites at every poll.

Before posting, refresh the head and discussion. If either changed, reconcile the new evidence and confirm that the finding still applies. Keep an accurate record of which revision was actually tested.

## Post findings without duplicates

A finding should identify a concrete trigger, explain the incorrect result and its impact, and point to a narrow relevant location. Include a minimal reproduction or other direct evidence when useful. Use the repository's severity convention. Separate unrelated causes; keep symptoms of one cause together.

Deduplicate by root cause and behavior, not wording or line number. Do not post an inherited finding again on a stacked PR. Refer to its existing thread when needed. Never reopen a resolved thread or re-post an already discussed issue merely because it remains present. Distinguish an independently demonstrated new regression from the old issue before reporting it.

Post only actionable findings supported by the review. If none remain, say that no new actionable issues were found and identify the reviewed revision, relevant checks, and material limits. Do not invent findings to fill a review. Avoid repeated comments on unchanged code.

## Follow existing threads

For each tracked unresolved finding, read the full thread and inspect the current code before acting:

| State | Action |
|---|---|
| No reply, fix verified | Resolve the thread. A reply is not required. |
| Reply present, fix verified | Read the reply, then resolve. Reply only if useful context is missing. |
| Reply claims a fix, but the issue remains | Push back in the same thread with the current reproduction or precise remaining gap. Keep it unresolved. |
| Reply explains an intentional design or disproves the finding | Evaluate the explanation against the contract. Acknowledge a mistaken finding and resolve it when the evidence warrants that. |
| No fix and no new reply or evidence | Leave the thread unchanged. |
| Verification is blocked or inconclusive | Keep it unresolved and state the concrete verification limit when relevant. |

Verify the original failing behavior and any important edge case of the proposed fix. A new commit, green CI, or an author's assurance alone is insufficient. Manage the tracked review threads; leave unrelated reviewers' threads alone unless the user includes them in scope.

## Monitor when requested

Unless the user specifies otherwise, poll every **10 minutes** and pause after **10 consecutive successful checks with no changes**. On resumption, reset the count and check immediately.

At each poll:

1. Rediscover open PRs if the scope is all open PRs. Fetch changed heads, bases, PR content, and discussions, including tracked threads on recently closed or merged PRs when follow-up is still relevant.
2. Review new PRs and changed code. Read new replies and apply the thread rules above.
3. Reset the unchanged count when relevant code, PR state, or discussion changes. Otherwise increment it after a successful complete check. Failed or incomplete checks do not count. Do not count missed intervals as checks.
4. Save the updated baseline after posting or resolving, so the reviewer's own already-processed actions do not appear as new author activity on the next poll.
5. At ten unchanged checks, record the paused state and stop. Honor an earlier user pause or stop immediately.

Wait between polls without busy polling. Stay interruptible and follow the environment's wait limits. Do not claim that monitoring will continue after the turn unless an actual scheduling mechanism has been configured and confirmed.

## Report progress and completion

During review, report meaningful findings, verified fixes, and remaining uncertainty. During monitoring, keep status updates brief and include the unchanged count when useful.

At the end, state whether monitoring is active, paused, or stopped. Link posted reviews and material unresolved findings, mention verified resolutions, and disclose relevant validation limits. Do not imply that untested changes were verified or that unresolved issues were fixed.
