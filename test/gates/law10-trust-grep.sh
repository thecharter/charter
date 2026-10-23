#!/usr/bin/env bash
# Gate for Law 10 (the kernel is the only trusted checker): no `sorry`,
# `native_decide`, or `axiom` in the language, the examples, or the executable.
set -u
cd "$(dirname "$0")/../.." || exit 2
hits=$(grep -rn "sorry\|native_decide\|axiom " src/Charter/ Examples/ src/Main.lean src/Charter.lean Examples.lean)
if [ -n "$hits" ]; then
  echo "$hits"
  echo "FAIL law10-trust-grep: the lines above name a trust escape"
  exit 1
fi
echo "ok   law10-trust-grep"
