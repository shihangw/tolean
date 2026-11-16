---
name: independent-code-reviewer
description: Independently review pull requests, post supported findings, and follow review threads through verified fixes without duplicating or reopening issues. Use for PR review and review follow-up; monitor repeatedly only when requested.
---

# Independent Code Reviewer

Act as an independent reviewer. Check the implementation against its contracts and base revision. Treat the author's description and claimed fixes as evidence to verify, not as conclusions to adopt. Do not wait for or read CI output; GitHub checks already inform the author.

Use the repository and PR scope the user specifies. Honor existing authorization to post comments, reply, and resolve threads; do not ask for it again. A request to create or edit this skill alone does not authorize GitHub actions.

Reviewer authority is comment-only: inline findings, thread replies, thread resolutions, and the review summary. Never submit an approval or a request-changes review, and never edit source, push, or merge as the reviewer.

Author and reviewer can share one GitHub login, so the login does not identify the reviewer. Identify this reviewer's comments by the comment IDs in the checkpoint and the reviewer's known conversation marker. The presence of some other `replit-nexus:cnv` marker does not make a comment the reviewer's.

## Establish the review state

- Read applicable repository instructions and relevant skills.
- Fetch the current head and base SHAs, diff, PR description, and complete discussion. Include resolved threads and author replies.
- Identify findings already raised on this PR and related PRs. For a stacked PR, compare against its declared base and distinguish inherited defects from new ones.
- Preserve a checkpoint with PR numbers, last reviewed head and base SHAs, finding summaries, thread IDs, root comment IDs, resolution state, relevant reply IDs, the reviewer's conversation marker, and the review summary comment ID and URL. Keep credentials out of it.

Keep four kinds of state distinct:

| State | Authority and purpose |
|---|---|
| Provider discovery | Live provider metadata and complete, paginated PR and discussion reads establish what exists and what changed. |
| Canonical review and assignment state | The checkpoint records active PRs, history, findings, assignments, reviewed revisions, processed replies, and pending work. A JSON entry does not establish platform tracking. |
| Platform association and watch | Replit's PR bindings and per-PR watch settings establish which PRs this conversation tracks and watches. A worker's binding is not a coordinator's binding. |
| Activity display | Cards and board links show progress to the user. They do not register a PR, enable watch, assign a reviewer, or schedule checks. |

On Replit, read `.local/skills/pr-delivery/SKILL.md` and its `references/watching.md` before handling association or watch. For a one-off review, associate the subject PR with verified live metadata, without requesting watch or creating a monitoring routine. Check and disclose any inherited watch setting; do not silently treat it as authorization for ongoing monitoring or change a conversation-wide preference. Association alone grants no review actions.

## Review independently

Read the changed code and the surrounding callers, invariants, and tests. Follow consequences across parsing, translation, evaluation, serialization, generated artifacts, and proofs when those layers are affected.

Review as an architect, from first principles, for correctness, complexity, and maintainability together. The PR must present a simple staged mental model that a reviewer with short context can follow; when it does not, say so plainly and name the code that needs explanation or simplification. Identify unnecessary complexity: duplicated traversals, special cases that should be one general rule, and edge cases that a simpler uniform rule would handle. Recommend separated responsibilities and extension without modifying existing behavior; a new constructor or case must never fall silently into a catch-all branch.

Have plain opinions on design choices. When a layer makes a design choice, say whether it is right and why, without hedging. Be blunt about the code, never about people. Reject band-aid fixes: when a change patches a symptom while the root cause remains, such as a traversal that returns false on unknown constructors or a conservative refusal that defers the real grammar rule, say so and name the real fix and its cost. Do not accept a deferral such as "left for the plan" as closing an issue when the deferral itself creates debt. Treat a contract that the code relies on but does not write down where the next author will find it, such as the value model, ownership, or refusal surface, as a maintainability defect.

Investigate likely defects with small reproductions. Compare with the base when it is unclear whether the change introduced the problem. Check the claimed contract before treating an intentional refusal or documented limitation as a bug. A passing proof establishes its stated proposition; inspect its assumptions and model as well as whether it compiles.

Use an isolated checkout or snapshot at the recorded head for experiments. Preserve the user's working tree. Run checks appropriate to the change where the tooling exists locally, as reproductions of the behavior under review. State the limit when Lean or the toolchain is unavailable. Broaden testing when a failure or unresolved concern warrants it. Do not rerun unchanged suites at every poll.

Before posting, refresh the head and discussion. If either changed, reconcile the new evidence and confirm that the finding still applies. Keep an accurate record of which revision was actually tested.

## Post findings without duplicates

A finding should identify a concrete trigger, explain the incorrect result and its impact, and point to a narrow relevant location. Include a minimal reproduction or other direct evidence when useful. Use the repository's severity convention. Separate unrelated causes; keep symptoms of one cause together.

Deduplicate by root cause and behavior, not wording or line number. Do not post an inherited finding again on a stacked PR. Refer to its existing thread when needed. Never reopen a resolved thread or re-post an already discussed issue merely because it remains present. Distinguish an independently demonstrated new regression from the old issue before reporting it.

Every point, defect or design, must be reachable under the code's contract, actionable with a discrete change, and introduced or worsened by the diff unless clearly labeled pre-existing. Do not speculate.

When the same defect class appears in more than one PR, post one structural comment on the newest PR that links the earlier instances and states the structural remedy. Do not repeat it on each PR.

Post only actionable findings supported by the review. If none remain, state that explicitly in the required review summary below. Do not invent findings to fill a review. Avoid repeated finding comments on unchanged code.

## Keep one review summary per PR

After every completed independent review, always publish a top-level summary comment on the PR, even when no issues were found. This must be a PR-level comment, not an inline comment or a review body.

Keep one summary comment per PR per reviewer. Create it after the first completed review. Whenever a later independent review round completes, edit that same comment in place rather than posting another summary. Read the checkpoint and the current PR comments before creating one. If the checkpoint lacks its ID, find this reviewer's existing summary first, identified as described above. Do not edit another reviewer's summary.

Use the heading `Independent review summary` and include only:

- `Reviewed:` the UTC date of the completed review round, as `YYYY-MM-DD`.
- `Head:` the first seven characters of the reviewed head SHA.
- For a long PR only (roughly more than 300 changed lines, or more than one subsystem), before `Result:`: one short paragraph on the goal or problem, and one on the behavior before versus after. Otherwise omit both.
- `Result:` each new finding, each finding from an earlier round that is still unresolved, and each verified resolution, as a short linked item. An unresolved actionable design defect belongs here too. If there are none, use the no-findings sentence below. If the review is blocked or incomplete, say so rather than claiming a clean result.
- `Design:` optional, after `Result:`. One bullet per additional design recommendation, one or two sentences each, linked to the inline comment that holds the detail. An unresolved defect must not appear only here. Omit the section when there are none.

Templates for completed reviews:

| With issues | Without issues |
| --- | --- |
| `## Independent review summary`<br><br>Reviewed: 2026-11-10<br>Head: `2f1f17f`<br><br>Result:<br>- New finding: [Short issue](FINDING_URL)<br>- Still unresolved: [Earlier issue](FINDING_URL)<br>- Verified resolution: [Short fix](RESOLUTION_URL)<br><br>Design:<br>- [Short objection](DESIGN_URL). One or two sentences on what is wrong and the remedy. | `## Independent review summary`<br><br>Reviewed: 2026-11-10<br>Head: `2f1f17f`<br><br>Result: No new issues were found. No resolutions were verified or performed. |

Replace the sample date, head and links. Carry every unresolved finding forward under `Result:` until it is resolved or withdrawn, so a later clean round never hides it. List new findings, resolutions and design points only from the completed round. Use the no-findings sentence only when no finding remains unresolved. Use the linked-item form when there are verified resolutions but no new findings; omit items and sections that do not apply. For a long PR, place the two context paragraphs between `Head:` and `Result:`.

Do not include base or merge-base SHAs, branch ancestry, review reasoning, validation inventories, CI summaries, or earlier-round history beyond the still-unresolved findings. Keep full revision details, validation evidence and limits in the checkpoint; put evidence for findings in their threads.

After each completed round, update the reviewed date, head and result in place. A formatting-only edit keeps the original review date. Record the summary comment ID and URL in the checkpoint after creating or editing it. Inline findings and useful thread replies supplement this summary; they do not replace it.

A status-only poll is not a new independent review round. Do not create duplicate summaries or edit the summary merely to report an unchanged poll.

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

Verify the original failing behavior and any important edge case of the proposed fix. A new commit or an author's assurance alone is insufficient.

Verify a code fix at the PR's own reviewed head. A plan entry, another branch, or a follow-up PR does not fix the defect at that head, so keep the thread unresolved there. Record the follow-up remediation separately, for example with a reply linking the PR that fixes the defect on the target branch. This rule does not prevent withdrawing a finding when evidence shows it was mistaken. Manage the tracked review threads; leave unrelated reviewers' threads alone unless the user includes them in scope.

## Monitor when requested

Use the user's authorized repositories, PR scope, cadence, and stop or pause conditions. Do not embed a particular repository, PR, worker, cursor, deadline, or cadence in this reusable procedure. Confirm an actual scheduling mechanism before claiming checks will continue after the turn. On resumption, check immediately and reset any agreed unchanged-check count.

### Reconcile platform coverage

For every in-scope open PR under authorized monitoring, including PRs already in the checkpoint:

1. Read live provider metadata. On GitHub, use `gh pr view <url> --json url,title,state,isDraft,updatedAt,headRefName,baseRefName,headRefOid`; use the equivalent provider fields elsewhere. Map OPEN to `draft` when `isDraft` is true, otherwise `open`; map terminal states to `merged` or `closed`.
2. In the conversation responsible for monitoring, call `associatePr({ url, title, state, updatedAt, headRef, baseRef, headSha, watch: true })` with those verified fields. Map `headRefName`, `baseRefName`, and `headRefOid` to `headRef`, `baseRef`, and `headSha`. Batch independent PRs with `associatePr({ pullRequests: [...] })`. Do not include incidental or out-of-scope PRs. For an explicit watch opt-out, associate without requesting watch and report polling-only coverage.
3. Verify with `listPrLinks({})` and `getPrWatchStatus({ urls: [...] })`. The former returns the newest 32 direct bindings, groups canonical aliases, excludes worker links, and contains last-known states, not live provider status. If `mayHaveMore` is true, absence from that window is not proof of no binding; use the association result and URL-specific watch status, and disclose any remaining verification limit. The no-argument watch call reads preferences, not links.
4. If a scoped PR is not tracked, repair its association from live metadata. If its watch is disabled, use `setPrWatch({ enabled: true, urls: [...] })` only within the user's monitoring authorization, then verify again. A chat preference can override `watch: true` on new associations. Never omit `urls`: that changes all tracked PRs and the default for future links. Respect an explicit user watch opt-out and report the coverage limit instead of overriding it.
5. Record verified coverage separately from review completion and assignment. If registration or verification fails, keep a pending repair and report the gap; do not claim active watch from a checkpoint entry, successful card display, or attempted registration.

Watched review comments can arrive as notifications. Do not promise that every comment or push will arrive, or that delivery is immediate. Notifications are wake-ups to reconcile live state, not a complete event log. Retain a scheduled provider-polling fallback for all authorized PRs and discussions even when watch is enabled. Do not read or wait for CI as part of independent review.

### Reconcile each check

1. If authorized for all open PRs, discover **all** open PRs in that scope, following provider pagination to exhaustion. Do not use only PRs absent from JSON or only the first page. Reconcile every result against assignments, pending work, and platform coverage, including already-known but unassigned or unassociated PRs. For a fixed PR scope, check every authorized PR without expanding it. Refresh tracked PRs with a live GET even when they disappear from the open listing; absence alone does not prove closure.
2. Fetch current heads, bases, PR content, and complete discussions, including resolved threads and replies. Follow every relevant discussion page. Continue reads for terminal PRs with pending audits or thread follow-up. Reconcile association and watch as above on every check; polling and notifications use the same checkpoint.
3. Persist pending routing before dispatching new work. Identify a code-review round by canonical PR identity and head/base SHAs, and a reply by its provider ID and any changed content or update version. Track pending, dispatched, and completed work separately. Reuse the recorded assignment for the same work key instead of creating another worker or review. If dispatch has an ambiguous result, reconcile the existing assignment or delivery before retrying; do not blindly resend it. A new head during review remains pending for a later round.
4. Route each new revision or reply once to its assigned reviewer, or review it directly when there is no delegated assignment. Review changed code, read new replies, and apply the existing thread rules. Record completion only after the reviewer reports the revision actually reviewed and the actions actually performed. Review completion does not end an authorized watch on an open PR.
5. Do not advance a processed cursor or successful-check baseline over a failed read, registration, or routing step. Preserve the last successful boundary and the pending gap; safely completed work stays deduplicated. Re-read the gap on retry. After a completed review round, create or edit its required summary, then save the processed baseline after comments, summary edits, and resolutions. Record their IDs so the reviewer's own actions do not look like new author activity.
6. Remove a PR from the active open list only after a live GET confirms merged or closed. Retain its history, findings, and pending work. Audit any unreviewed final head; for a merge, also inspect the landed change on the actual target revision, recording what was checked and any unavailable evidence. Keep own-head fix verification distinct from landed remediation. A terminal PR does not cancel these audits or close a stack; close the stack only after every member is terminal and required audits and follow-up are complete.
7. Reset any agreed unchanged count when relevant code, PR state, discussion, assignment, or coverage changes. Increment it only after a successful complete check with no changes. Failed or incomplete checks and missed intervals do not count. Honor the user's pause or stop immediately; record pending work and the actual schedule and watch state rather than claiming all activity stopped when a subscription remains enabled.

Wait between scheduled checks without busy polling. Stay interruptible and follow the environment's wait limits. If scheduling or provider access is unavailable, report monitoring as incomplete or paused, preserve pending work, and name the missing coverage.

### Clean up without losing follow-up

During authorized cleanup, call `listPrLinks({})` in each responsible conversation and verify each candidate's current provider state before `unassociatePr({ url })`. Unlink only confirmed merged or closed PRs, never open PRs. Keep terminal PRs with unfinished audits or replies in canonical pending state and the polling fallback even after unlinking; unlinking does not erase findings or finish an audit.

If `mayHaveMore` is true, repeat after removing eligible terminal links. There is no cursor through the older bindings: if no returned link can be removed, report cleanup as incomplete rather than unlinking open PRs to reach older ones. A coordinator's list excludes worker links, so worker cleanup must inspect the worker's own bindings.

Archive an idle reviewer only when it has no open PR assignment, pending routing, audit, reply, or other unfinished assignment, and when worker archival is authorized. Preserve its checkpoint and findings before archival. Neither a clean review nor a merged PR alone makes the worker idle.

### Process regression cases

When changing this procedure, check these cases without enabling watch or posting comments merely to test it:

| Case | Required outcome |
|---|---|
| Newly discovered, untracked open PR | Complete paginated discovery; persist assignment and pending work; associate and verify authorized watch before reporting coverage. |
| PR already in JSON but missing platform association | Repair association and verify URL-specific watch; do not skip it as already known or mistake an Activity link for coverage. |
| Associated PR with disabled watch | Repair only the authorized PR's watch and verify; preserve explicit opt-outs and global defaults. |
| Repeated latest head or reply from polling and notifications | Reuse the same work key and assignment; route once, keep newer work pending, and do not duplicate findings or summaries. |
| Merged PR with a pending final audit | Remove from the live open list after GET; retain final-head and landed audits, findings, and history; keep its stack unfinished until audited. |
| Idle worker cleanup | Archive only with authorization and no open or unfinished assignment; do not lose pending follow-up or another PR's work. |
| Failed read, registration, or routing | Preserve the gap and successful boundary, retry pending work without duplicating completed actions, and report incomplete coverage. |
| One-off review without monitoring authorization | Associate the subject without requesting watch or scheduling a routine; disclose inherited watch and do not change global preferences. |

## Report progress and completion

During review, report meaningful findings, verified fixes, and remaining uncertainty. During monitoring, keep status updates brief and include the unchanged count when useful.

At the end, report review completion separately from monitoring: not requested, active, incomplete, paused, or stopped. Claim active monitoring only with verified in-scope association and watch plus a confirmed polling fallback. State subscription or scheduling limits separately. Link posted reviews and material unresolved findings, mention verified resolutions, and disclose relevant validation limits. Do not imply that untested changes were verified or that unresolved issues were fixed.
