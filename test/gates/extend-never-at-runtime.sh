#!/usr/bin/env bash
# Law 14 / D11 Gate (`extend-never-at-runtime`):
# Verifies that `Extend` remains strictly a static/declaration-time construct (`Resolve/Static.lean`),
# never invoked by the live runtime term/trigger evaluator (`src/Charter/Eval/Eval.lean`).
set -u
cd "$(dirname "$0")/../.." || exit 2

if grep -qE 'applyExt|typeExt' src/Charter/Eval/Eval.lean; then
  echo "FAIL extend-never-at-runtime: Eval/Eval.lean references static typeExt/applyExt"
  exit 1
fi
echo "ok   extend-never-at-runtime (Eval/Eval.lean invokes zero static Extend paths)"
