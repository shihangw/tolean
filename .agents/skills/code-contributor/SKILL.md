---
name: code-contributor
description: Watch the pull requests you opened until they settle, answering each review comment and CI failure. Use after you open or push a PR, or when asked to monitor PRs or check comments.
---

# Watching your pull requests

A PR is yours to **tend** from the first push until it merges or closes: every review thread gets a fix or a reasoned reply, and every red CI check gets fixed.

## Steps

1. **Pick the wake source.** Push beats polling.
   - Push: when the session delivers GitHub activity for subscribed PRs (a `ReadNotifications` tool, or notices that PR activity is pending), subscribe to each PR and wait for those notices. Read them with `ReadNotifications` before anything else.
   - Poll: otherwise run [`watch-prs.sh`](watch-prs.sh) with Bash `run_in_background`. It checks every 10 minutes for 10 rounds and exits at the first new review, comment or finished CI check, which wakes you. Seed its state first, so only newer activity counts:
     ```sh
     ROUNDS=0 .agents/skills/code-contributor/watch-prs.sh "$CLAUDE_JOB_DIR/tmp/prs.seen" 58 59 60
     .agents/skills/code-contributor/watch-prs.sh "$CLAUDE_JOB_DIR/tmp/prs.seen" 58 59 60
     ```
     Skip the seeding run when you start by answering what is already there (step 2), and seed after that.
   Done when a watch is armed for every open PR you own.

2. **Triage each new item**, oldest first. Read the whole thread and reproduce the claim before you judge it.
   - Real: fix it on the lowest branch of a stack that has the bug, add a corpus or test case that fails without the fix, run the checks in `AGENTS.md` and the skills it names, push, then merge that branch into each PR stacked on it (merge; a pushed branch is never rewritten).
   - Not real, or already fixed: reply with the evidence, such as the commit that fixed it, the command and its output, or the spec section.
   - Out of scope: reply with where it goes instead (a follow-up PR, or the plan's open questions).
   - A red check: read its log (`gh run view <id> --log-failed`), fix the cause, push.
   Done when every new item has a reply in its own thread that names the commit or the evidence.

3. **Re-arm** the watch from step 1, with the same state file. Stop when every PR has merged or closed, or when a full watch (10 rounds) ends quietly; then report each PR's state: merged, waiting on review, or red, with its link.

## Reference

- Reply in the thread the comment opened: `gh api repos/{owner}/{repo}/pulls/<n>/comments/<id>/replies -f body=…` for a review comment, `gh pr comment <n>` for a review or an issue comment.
- `watch-prs.sh` exits 0 with the new items on stdout, 3 when all rounds pass quietly, 2 when `gh` cannot see the repository. `INTERVAL` (seconds) and `ROUNDS` change the defaults.
- A fix on a stacked PR's base reaches the PRs above it only after the merge into each; check their CI too.
