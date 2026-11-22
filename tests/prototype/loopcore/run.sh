#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
lake build tolean.Prototype.LoopCore.Examples tolean.Prototype.LoopCore.GoExamples \
  tolean.Prototype.LoopCore.TypeScript
lake env lean --run tests/prototype/loopcore/Print.lean |
  awk -v dir="$tmp" '/^--- / {file=dir "/" $2; next} {print >file}'
for file in sum_c find_c clamp_sum_c sum_cpp find_cpp two_loops_cpp; do
  diff -u "tests/prototype/loopcore/$file.lean" "$tmp/$file.lean"
  case "$file" in
    sum_c|sum_cpp) expected=10; input='[1,2,3,4]' ;;
    find_c) expected=2; input='[1,2,3,4]' ;;
    find_cpp) expected=3; input='[1,2,3,4]' ;;
    clamp_sum_c) expected=5; input='[-1,2,3,4]' ;;
    two_loops_cpp) expected=13; input='[1,2,3,4]' ;;
  esac
  printf '\nexample : %s %s 3 4 = %s := by decide\n' "$file" "$input" "$expected" >> "$tmp/$file.lean"
  lake env lean "$tmp/$file.lean"
done
for spec in sum.go:10 find.go:3 clamp_sum.go:5; do
  file=${spec%:*}
  expected=${spec#*:}
  actual=$(go run "tests/prototype/loopcore/$file")
  test "$actual" = "$expected" || { echo "$file: expected $expected, got $actual"; exit 1; }
  echo "$file: $actual (source interpreter only; no Go translation proof)"
done
for spec in sum.c:10 find.c:2 clamp_sum.c:5 sum.cpp:10 find.cpp:3 two_loops.cpp:13; do
  file=${spec%:*}
  expected=${spec#*:}
  case "$file" in
    *.cpp) "${CXX:-c++}" -std=c++17 -Wall -Wextra -Werror "tests/prototype/loopcore/$file" -o "$tmp/test" ;;
    *) "${CC:-cc}" -std=c11 -Wall -Wextra -Werror "tests/prototype/loopcore/$file" -o "$tmp/test" ;;
  esac
  actual=$("$tmp/test")
  test "$actual" = "$expected" || { echo "$file: expected $expected, got $actual"; exit 1; }
  echo "$file: $actual"
done
