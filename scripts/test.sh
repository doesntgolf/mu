#!/bin/sh
# Runs each tests/*.mu and compares its output against the .mu.expect file
# next to it. With --update, rewrites the .mu.expect files instead; review
# the changes with `git diff tests/`.
#
# usage: scripts/test.sh [--update] [tests/foo.mu ...]
# The interpreter is $MU, or ./a.out by default.

mu=${MU:-./a.out}
update=
if [ "$1" = --update ]; then
  update=1
  shift
fi
[ $# -eq 0 ] && set -- tests/*.mu

failed=0
for test in "$@"; do
  actual=$("$mu" "$test" 2>&1)
  if [ -n "$update" ]; then
    printf '%s\n' "$actual" > "$test.expect"
  elif ! printf '%s\n' "$actual" | diff -u --label "$test.expect" --label actual "$test.expect" -; then
    failed=$((failed + 1))
  fi
done

[ -n "$update" ] && exit 0
echo "$(($# - failed)) of $# tests passed"
[ "$failed" -eq 0 ]
