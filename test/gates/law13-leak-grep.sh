#!/usr/bin/env bash
# Gate for Law 13 / goal 2 (the language names no institution): nothing under
# src/Charter/ names an example program. The exclusions are generic vocabulary
# of the standard library (a commons pool is a pattern, not the Autonomous Commons).
set -u
cd "$(dirname "$0")/../.." || exit 2
hits=$(grep -rniE "sovereign|\bpsa\b|commons" src/Charter/ src/Charter.lean | grep -viE "commons pool|commonsShare|commonsAllocated|toCommons|Autonomous_Commons")
if [ -n "$hits" ]; then
  echo "$hits"
  echo "FAIL law13-leak-grep: the language layer names an example"
  exit 1
fi
echo "ok   law13-leak-grep"
