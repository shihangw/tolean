#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
lake build --wfail tolean.Experimental.LoopCore.Examples
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
lake env lean --run tests/experimental/loopcore/Print.lean > "$tmp/printed"
diff -u tests/experimental/loopcore/expected.txt "$tmp/printed"
awk -v dir="$tmp" '/^--- / {file=dir "/" $2; next} {print >file}' "$tmp/printed"
for file in sum_c find_c clamp_sum_c sum_cpp find_cpp two_loops_cpp \
    repeated_c repeated_cpp branches_c branches_cpp; do
  case "$file" in
    sum_c|sum_cpp) expected=10; input='[1,2,3,4]' ;;
    find_c) expected=2; input='[1,2,3,4]' ;;
    find_cpp) expected=3; input='[1,2,3,4]' ;;
    clamp_sum_c) expected=5; input='[-1,2,3,4]' ;;
    two_loops_cpp) expected=13; input='[1,2,3,4]' ;;
    repeated_*|branches_*) expected=2; input='[1,2,3,4]' ;;
  esac
  printf '\nexample : %s %s 3 4 = %s := by decide\n' \
    "$file" "$input" "$expected" >> "$tmp/$file.lean"
  printf '\n#eval %s %s 3 4\n' "$file" "$input" >> "$tmp/$file.lean"
  output=$(lake env lean "$tmp/$file.lean")
  printf '%s\n' "$output"
  actual=$(printf '%s\n' "$output" | tail -n 1)
  test "$actual" = "$expected" || {
    echo "$file: expected $expected, got $actual"
    exit 1
  }
done
