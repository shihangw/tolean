#!/usr/bin/env bash
# Wait for new activity on pull requests: a review, a review comment, an issue
# comment, or a CI check that reached a final state. Polls every INTERVAL
# seconds (default 600) for at most ROUNDS rounds (default 10).
#
# usage: watch-prs.sh <state-file> <pr>...
#
# Prints one line per new item and exits 0 at the first round that has any.
# Exits 3 when every round passes quietly. The state file keeps what was
# already seen, so the next run reports only what is newer. Run it once with a
# fresh state file and ROUNDS=0 to mark everything that exists as seen.
set -uo pipefail
state=$1; shift
interval=${INTERVAL:-600}
rounds=${ROUNDS:-10}
repo=$(gh repo view --json nameWithOwner -q .nameWithOwner) || exit 2
touch "$state"

snapshot() {
  for n in "$@"; do
    gh api "repos/$repo/pulls/$n/reviews" \
      --jq ".[] | \"#$n review \(.id) \(.user.login) \(.state): \(.body | gsub(\"\\n\"; \" \") | .[0:200])\"" || true
    gh api "repos/$repo/pulls/$n/comments" \
      --jq ".[] | \"#$n comment \(.id) \(.user.login) \(.path):\(.line // .original_line): \(.body | gsub(\"\\n\"; \" \") | .[0:200])\"" || true
    gh api "repos/$repo/issues/$n/comments" \
      --jq ".[] | \"#$n issue-comment \(.id) \(.user.login): \(.body | gsub(\"\\n\"; \" \") | .[0:200])\"" || true
    # A check counts once it passes or fails; the head commit names the run.
    head=$(gh pr view "$n" --json headRefOid -q .headRefOid 2>/dev/null || true)
    gh pr checks "$n" --json name,bucket \
      --jq ".[] | select(.bucket != \"pending\") | \"#$n check ${head:0:7}/\(.name) \(.bucket)\"" 2>/dev/null || true
  done
}

# The key of a line is everything before its first ':' or, for checks, the
# whole line, so an edited comment body does not count as new.
key() { sed -E 's/^(#[0-9]+ (review|comment|issue-comment) [0-9]+).*/\1/'; }

check_new() {
  current=$(snapshot "$@")
  new=$(comm -13 <(key <"$state" | sort -u) <(printf '%s\n' "$current" | key | sort -u))
  if [ -n "$new" ]; then
    printf '%s\n' "$current" | grep -F -f <(printf '%s\n' "$new") || true
    printf '%s\n' "$current" >>"$state"
    return 0
  fi
  return 1
}

if [ "$rounds" -eq 0 ]; then
  snapshot "$@" >>"$state"
  exit 0
fi
for ((i = 1; i <= rounds; i++)); do
  check_new "$@" && exit 0
  [ "$i" -lt "$rounds" ] && sleep "$interval"
done
echo "no new activity after $rounds rounds"
exit 3
