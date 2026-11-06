#!/usr/bin/env bash
# Gate for Law 11 (the author never sees Lean): run the binary the way an author
# does and grep everything it prints, on success and on failure, for the engine.
# The binary must already be built (tools/battery builds it first).
set -u
cd "$(dirname "$0")/../.." || exit 2
B=.lake/build/bin/charter
if [ ! -x "$B" ]; then echo "FAIL law11-no-engine-in-output: $B is not built"; exit 2; fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
printf 'this is not a program\n' > "$tmp/bad.charter"
printf 'Fact x Identified by Int\n?x(1\n' > "$tmp/bad.eflint"
TEN=Examples/Tenancy/tenancy.charter
COM=Examples/AutonomousCommons/commons.charter
ESC=Examples/ServiceEscrow/service-escrow.charter
{
  "$B" help
  "$B" version
  "$B" check "$TEN" "$COM" "$ESC"
  "$B" check
  "$B" trace T.1 "$TEN"
  "$B" trace SE.2 "$ESC"
  "$B" trace NO_SUCH_CLAUSE "$TEN"
  "$B" run "$TEN"
  "$B" no-such-command
  "$B" check "$tmp/missing.charter"
  "$B" check "$tmp/bad.charter"
  "$B" run "$tmp/bad.eflint"
  "$B" test "$tmp/bad.eflint"
} > "$tmp/out.txt" 2>&1
hits=$(grep -niE '\blean\b|\blake\b|olean|lakefile|\btactic\b|\bsorry\b|_lean_|lean_' "$tmp/out.txt")
if [ -n "$hits" ]; then
  echo "$hits"
  echo "FAIL law11-no-engine-in-output: author-visible output names the engine"
  exit 1
fi
echo "ok   law11-no-engine-in-output ($(wc -l < "$tmp/out.txt" | tr -d ' ') lines checked)"
