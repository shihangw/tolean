#!/usr/bin/env bash
# Deletes GitHub Actions caches that no run will restore again, so the
# repository stays under GitHub's 10 GB cache limit. Above the limit,
# GitHub evicts caches itself, and it can evict the ones still in use.
#
#   prune-caches.sh <ref>        keeps the newest cache of each kind on <ref>
#   prune-caches.sh --all <ref>  deletes every cache on <ref>
#
# <ref> is a git ref as GitHub names a cache's scope, such as
# refs/heads/main or refs/pull/42/merge. A cache's kind is its key without
# the hashes: lake-Linux, translator-wasm or lean-wasm. A run restores the
# exact key or else the newest cache of that kind, so on one ref only the
# newest cache of each kind is ever restored. The others only take space.
#
# Without --all, a cache that a run used in the last 30 minutes stays, so a
# run that is still going keeps the cache it restored.
#
# Needs GH_TOKEN with `actions: write` and GITHUB_REPOSITORY. With DRY_RUN
# set, it prints what it would delete and deletes nothing.
set -euo pipefail

all=false
if [ "${1:-}" = --all ]; then
  all=true
  shift
fi
ref=$1
# GNU date on the runner, BSD date on macOS.
cutoff=$(date -u -d '30 minutes ago' +%Y-%m-%dT%H:%M:%SZ 2>/dev/null ||
  date -u -v-30M +%Y-%m-%dT%H:%M:%SZ)

# One line per cache on the ref, most recently used first. A ref holds far
# fewer than 100 caches once this script runs after each CI run.
#
# A branch name may contain & and =, so gh encodes the query with -f.
# Pasted into the URL as it is, refs/heads/a&ref=refs/heads/main would add
# a second ref parameter and select main's caches. For the same reason, the
# loop skips any cache whose ref is not exactly <ref>.
gh api --method GET "repos/$GITHUB_REPOSITORY/actions/caches" \
  -f ref="$ref" -f per_page=100 -f sort=last_accessed_at -f direction=desc \
  -q '.actions_caches[] | "\(.id) \(.ref) \(.last_accessed_at) \(.size_in_bytes) \(.key)"' |
  {
    seen=" "
    while read -r id cache_ref accessed size key; do
      if [ "$cache_ref" != "$ref" ]; then
        echo "skip $key, which belongs to $cache_ref"
        continue
      fi
      kind=$(sed -E 's/-[0-9a-f]{32,}//g' <<<"$key")
      if ! $all; then
        if [[ $seen != *" $kind "* ]]; then
          seen="$seen$kind "
          echo "keep $key"
          continue
        fi
        if [[ ! $accessed < $cutoff ]]; then
          echo "keep $key, used in the last 30 minutes"
          continue
        fi
      fi
      echo "delete $key ($((size / 1048576)) MB)"
      [ -n "${DRY_RUN:-}" ] ||
        gh api -X DELETE "repos/$GITHUB_REPOSITORY/actions/caches/$id" >/dev/null
    done
  }
