#!/usr/bin/env bash
# Wait for new activity on pull requests: a review, a review comment, an issue
# comment, or a CI check that reached a final state. Polls every INTERVAL
# seconds (default 600) for at most ROUNDS rounds (default 10).
#
# usage: watch-prs.sh <state-file> <pr>...
#
# Prints one line per new item and exits 0 at the first round that has any.
# A seeding run (ROUNDS=0) prints what is open already: the checks that are
# red and the review threads that are not resolved.
# Exits 3 when every round fetched everything and found nothing new, and 4
# when some round could not fetch, so its silence proves nothing. The state
# file keeps what was already seen, so the next run reports only what is
# newer. Run it once with a fresh state file and ROUNDS=0 to mark everything
# that exists as seen.
set -uo pipefail
state=$1; shift
interval=${INTERVAL:-600}
rounds=${ROUNDS:-10}
repo=$(gh repo view --json nameWithOwner -q .nameWithOwner) || exit 2
touch "$state"
failed=$(mktemp)
trap 'rm -f "$failed"' EXIT

# One listing, every page of it. A failure marks the snapshot incomplete.
list() {
  gh api --paginate "$1" --jq "$2" || echo "$1" >>"$failed"
}

# The review threads of PR $1 that no one has resolved, one line each. The
# reviewer resolves a thread when its finding is settled, so an open thread
# may still need an answer even when it has replies.
unresolved() {
  gh api graphql -F owner="${repo%/*}" -F name="${repo#*/}" -F n="$1" -f query='
    query($owner: String!, $name: String!, $n: Int!) {
      repository(owner: $owner, name: $name) {
        pullRequest(number: $n) {
          reviewThreads(first: 100) {
            nodes { isResolved comments(first: 1) { nodes { databaseId path body } } }
          }
        }
      }
    }' --jq ".data.repository.pullRequest.reviewThreads.nodes[] | select(.isResolved | not)
      | .comments.nodes[0] | \"#$1 unresolved \(.databaseId) \(.path): \(.body | gsub(\"\\n\"; \" \") | .[0:200])\"" \
    || echo "unresolved threads of #$1" >>"$failed"
}

snapshot() {
  for n in "$@"; do
    list "repos/$repo/pulls/$n/reviews" \
      ".[] | \"#$n review \(.id) \(.user.login) \(.state): \(.body | gsub(\"\\n\"; \" \") | .[0:200])\""
    list "repos/$repo/pulls/$n/comments" \
      ".[] | \"#$n comment \(.id) \(.user.login) \(.path):\(.line // .original_line): \(.body | gsub(\"\\n\"; \" \") | .[0:200])\""
    list "repos/$repo/issues/$n/comments" \
      ".[] | \"#$n issue-comment \(.id) \(.user.login): \(.body | gsub(\"\\n\"; \" \") | .[0:200])\""
    # A check counts once it passes or fails; the head commit names the run.
    head=$(gh pr view "$n" --json headRefOid -q .headRefOid) || { echo "head of #$n" >>"$failed"; continue; }
    # `gh pr checks` exits nonzero when a check failed or is pending, and when
    # the PR has no checks yet. Only an error message beyond those counts as
    # a failed fetch.
    err=$(mktemp)
    gh pr checks "$n" --json name,bucket \
      --jq ".[] | select(.bucket != \"pending\") | \"#$n check ${head:0:7}/\(.name) \(.bucket)\"" 2>"$err"
    if [ -s "$err" ] && ! grep -q "no checks reported" "$err"; then echo "checks of #$n" >>"$failed"; fi
    rm -f "$err"
  done
}

# The key of a line is everything before its first ':' or, for checks, the
# whole line, so an edited comment body does not count as new.
key() { sed -E 's/^(#[0-9]+ (review|comment|issue-comment) [0-9]+).*/\1/'; }

# 0: new items printed; 1: nothing new; 2: the snapshot is incomplete.
check_new() {
  : >"$failed"
  current=$(snapshot "$@")
  new=$(comm -13 <(key <"$state" | sort -u) <(printf '%s\n' "$current" | key | sort -u))
  if [ -n "$new" ]; then
    printf '%s\n' "$current" | grep -F -f <(printf '%s\n' "$new") || true
    printf '%s\n' "$current" >>"$state"
    return 0
  fi
  [ -s "$failed" ] && return 2
  return 1
}

if [ "$rounds" -eq 0 ]; then
  # Seeding marks everything as seen, so print the checks that are red now:
  # the watch would never report them.
  : >"$failed"
  current=$(snapshot "$@")
  if [ -s "$failed" ]; then
    echo "could not fetch: $(paste -sd, "$failed")" >&2
    exit 4
  fi
  open=$(for n in "$@"; do unresolved "$n"; done)
  if [ -s "$failed" ]; then
    echo "could not fetch: $(paste -sd, "$failed")" >&2
    exit 4
  fi
  printf '%s\n' "$current" >>"$state"
  printf '%s\n' "$current" | grep ' check .* fail$' || true
  [ -n "$open" ] && printf '%s\n' "$open"
  exit 0
fi
incomplete=0
for ((i = 1; i <= rounds; i++)); do
  check_new "$@"
  case $? in
    0) exit 0 ;;
    2) incomplete=$((incomplete + 1)); echo "round $i: could not fetch $(paste -sd, "$failed")" >&2 ;;
  esac
  [ "$i" -lt "$rounds" ] && sleep "$interval"
done
if [ "$incomplete" -gt 0 ]; then
  echo "no new activity seen, but $incomplete of $rounds rounds could not fetch everything"
  exit 4
fi
echo "no new activity after $rounds rounds"
exit 3
