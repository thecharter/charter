#!/usr/bin/env bash
# Law 14 / §3a Gate (`replay`, G4.2, T36):
# 1. Compiles `Examples/ServiceEscrow/service-escrow.charter` to a signed `.artifact`.
# 2. Drives two independent `charter-server` processes with identical JSON event streams and
#    asserts identical `stateRoot` and verdict histories.
# 3. Verifies offline `charter-server replay <artifact> <log>` and snapshot+tail replay agree,
#    and verifies that tampering a log entry causes `replay` to fail loudly.
set -u
cd "$(dirname "$0")/../.." || exit 2
B=.lake/build/bin/charter
SB=.lake/build/bin/charter-server
[ -x "$B" ] && [ -x "$SB" ] || { echo "FAIL replay: binaries missing"; exit 2; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

"$B" build Examples/ServiceEscrow/service-escrow.charter -o "$tmp/escrow.artifact" >/dev/null 2>&1 || {
  echo "FAIL replay: charter build failed"; exit 1;
}

cat > "$tmp/requests.jsonl" <<'EOF'
{"op":"ExercisePower","action":"initiate-emergency-freeze","args":["SecAudit","Acme",100]}
{"op":"ExercisePower","action":"suspend-under-freeze","args":["CloudCo","Acme"]}
{"op":"AdvanceClock","newTime":2}
{"op":"ExercisePower","action":"dismiss-freeze","args":["NeutralArb","Acme"]}
{"op":"GetState"}
EOF

"$SB" serve "$tmp/escrow.artifact" --log "$tmp/run1.log" --snapshot "$tmp/run1.snap" < "$tmp/requests.jsonl" > "$tmp/out1.jsonl" || {
  echo "FAIL replay: server 1 exited non-zero"; exit 1;
}
"$SB" serve "$tmp/escrow.artifact" --log "$tmp/run2.log" < "$tmp/requests.jsonl" > "$tmp/out2.jsonl" || {
  echo "FAIL replay: server 2 exited non-zero"; exit 1;
}

if ! cmp -s "$tmp/out1.jsonl" "$tmp/out2.jsonl"; then
  echo "FAIL replay: two server runs diverged on identical artifact + history"
  diff -u "$tmp/out1.jsonl" "$tmp/out2.jsonl"
  exit 1
fi

rep1=$("$SB" replay "$tmp/escrow.artifact" "$tmp/run1.log" 2>&1); st1=$?
rep2=$("$SB" replay "$tmp/escrow.artifact" "$tmp/run1.log" --snapshot "$tmp/run1.snap" 2>&1); st2=$?
if [ "$st1" -ne 0 ] || [ "$st2" -ne 0 ] || [ "$rep1" != "$rep2" ]; then
  echo "FAIL replay: genesis replay and snapshot replay disagreed"
  echo "genesis: $rep1"
  echo "snap:    $rep2"
  exit 1
fi

# Tamper with the log and verify `replay` rejects it
python3 -I - "$tmp/run1.log" "$tmp/tampered.log" <<'PY'
import pathlib, sys
txt = pathlib.Path(sys.argv[1]).read_text()
pathlib.Path(sys.argv[2]).write_text(txt.replace('"newTime":2', '"newTime":1'))
PY

if "$SB" replay "$tmp/escrow.artifact" "$tmp/tampered.log" >/dev/null 2>&1; then
  echo "FAIL replay: tampered log was unexpectedly accepted!"
  exit 1
fi

echo "ok   replay (byte-identical dual-server execution, snapshot parity, and tamper rejection)"
