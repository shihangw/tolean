#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
lake build tolean.Prototype.LoopCore.Examples tolean.Prototype.LoopCore.Go \
  tolean.Prototype.LoopCore.TypeScript
lake env lean --run tests/prototype/loopcore/Print.lean |
  awk -v dir="$tmp" '/^--- / {file=dir "/" $2; next} {print >file}'
for file in sum_c find_c clamp_sum_c sum_cpp find_cpp two_loops_cpp; do
  diff -u "tests/prototype/loopcore/$file.lean" "$tmp/$file.lean"
  lake env lean "tests/prototype/loopcore/$file.lean"
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
