#!/usr/bin/env bash
# Law 14 / §3a Gate (`certificate-at-office`, G4.1, G4.3, B10, D27, T24):
# 1. No `.artifact` takes office in `charter-server` without a valid SHA-256 + HMAC certificate;
#    a tampered `.artifact` is refused naming its hash mismatch.
# 2. A runtime `AmendLaw` transition refuses an uncertified successor artifact, refuses a
#    certified successor when active `Immunity ... Against Amend` blocks weakening, and installs
#    a certified non-weakening successor artifact when authorized.
set -u
cd "$(dirname "$0")/../.." || exit 2
B=.lake/build/bin/charter
SB=.lake/build/bin/charter-server
[ -x "$B" ] && [ -x "$SB" ] || { echo "FAIL certificate-at-office: binaries missing"; exit 2; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cat > "$tmp/v1.charter" <<'EOF'
Fact council Identified by C1.
Fact member Identified by Ava.
Fact quorum Identified by council.
Fact fee-active Identified by council.
Fact exited Identified by member.

Power exit-right Actor member
  Holds when True
  Valid when True
  Creates exited(member).

Immunity protect-exit Holder member
  Against Amend
  Protects exit-right
  Holds when True.

Amend update-fee-rule Actor council
  Holds when quorum(council)
  Valid when quorum(council).

+quorum(C1).
EOF

cat > "$tmp/v2_good.charter" <<'EOF'
Fact council Identified by C1.
Fact member Identified by Ava.
Fact quorum Identified by council.
Fact fee-active Identified by council.
Fact exited Identified by member.

Power exit-right Actor member
  Holds when True
  Valid when True
  Creates exited(member).

Power toggle-fee Actor council
  Holds when quorum(council)
  Valid when quorum(council)
  Creates fee-active(council).

Immunity protect-exit Holder member
  Against Amend
  Protects exit-right
  Holds when True.

Amend update-fee-rule Actor council
  Holds when quorum(council)
  Valid when quorum(council).

+quorum(C1).
EOF

cat > "$tmp/v2_weaken_entrenched.charter" <<'EOF'
Fact council Identified by C1.
Fact member Identified by Ava.
Fact quorum Identified by council.
Fact fee-active Identified by council.
Fact exited Identified by member.

Power exit-right Actor member
  Holds when True
  Valid when True
  Creates exited(member).

Amend update-fee-rule Actor council
  Holds when quorum(council)
  Valid when quorum(council).

+quorum(C1).
EOF

"$B" build "$tmp/v1.charter" -o "$tmp/v1.artifact" --sign-key "prod-key-1" >/dev/null 2>&1 || exit 1
"$B" build "$tmp/v2_good.charter" -o "$tmp/v2_good.artifact" --sign-key "prod-key-1" >/dev/null 2>&1 || exit 1
"$B" build "$tmp/v2_weaken_entrenched.charter" -o "$tmp/v2_bad.artifact" --sign-key "prod-key-1" >/dev/null 2>&1 || exit 1
"$B" build "$tmp/v2_good.charter" -o "$tmp/v2_wrong_key.artifact" --sign-key "wrong-attacker-key" >/dev/null 2>&1 || exit 1

# 1. Tamper payload of v1.artifact -> must refuse and name hash mismatch
python3 -I - "$tmp/v1.artifact" "$tmp/v1_tampered.artifact" <<'PY'
import pathlib, sys
txt = pathlib.Path(sys.argv[1]).read_text()
pathlib.Path(sys.argv[2]).write_text(txt.replace('"version": 0', '"version": 99'))
PY

tamper_out=$("$SB" verify "$tmp/v1_tampered.artifact" --key "prod-key-1" 2>&1); tamper_st=$?
if [ "$tamper_st" -eq 0 ] || ! printf '%s\n' "$tamper_out" | grep -q 'artifact hash mismatch.*sha256:'; then
  echo "FAIL certificate-at-office: tampered artifact was not refused with hash named"
  printf '%s\n' "$tamper_out"
  exit 1
fi

# 2. Wrong-key artifact refused at office
wrong_out=$("$SB" verify "$tmp/v2_wrong_key.artifact" --key "prod-key-1" 2>&1); wrong_st=$?
if [ "$wrong_st" -eq 0 ]; then
  echo "FAIL certificate-at-office: wrong-key signature accepted!"
  exit 1
fi

# 3. Runtime AmendLaw refuses wrong-key successor, refuses entrenched-weakening successor, accepts certified good successor
cat > "$tmp/amend_reqs.jsonl" <<EOF
{"op":"AmendLaw","amendAct":"update-fee-rule","args":["C1"],"successorArtifact":"$tmp/v2_wrong_key.artifact"}
{"op":"AmendLaw","amendAct":"update-fee-rule","args":["C1"],"successorArtifact":"$tmp/v2_bad.artifact"}
{"op":"AmendLaw","amendAct":"update-fee-rule","args":["C1"],"successorArtifact":"$tmp/v2_good.artifact"}
{"op":"ExercisePower","action":"toggle-fee","args":["C1"]}
EOF

res=$("$SB" serve "$tmp/v1.artifact" --key "prod-key-1" < "$tmp/amend_reqs.jsonl")
line1=$(printf '%s\n' "$res" | sed -n '1p')
line2=$(printf '%s\n' "$res" | sed -n '2p')
line3=$(printf '%s\n' "$res" | sed -n '3p')
line4=$(printf '%s\n' "$res" | sed -n '4p')

if ! (printf '%s\n' "$line1" | grep -q '"ok":false' && printf '%s\n' "$line1" | grep -q 'signature verification failed'); then
  echo "FAIL certificate-at-office: wrong-key AmendLaw was not refused: $line1"; exit 1
fi
if ! (printf '%s\n' "$line2" | grep -q '"ok":false' && printf '%s\n' "$line2" | grep -q 'removes entrenched protection'); then
  echo "FAIL certificate-at-office: weakening AmendLaw was not refused: $line2"; exit 1
fi
if ! (printf '%s\n' "$line3" | grep -q '"ok":true' && printf '%s\n' "$line3" | grep -q '"outcome":"Allow"'); then
  echo "FAIL certificate-at-office: valid certified AmendLaw failed: $line3"; exit 1
fi
if ! (printf '%s\n' "$line4" | grep -q '"ok":true' && printf '%s\n' "$line4" | grep -q '"outcome":"Allow"'); then
  echo "FAIL certificate-at-office: new rule toggle-fee did not take office: $line4"; exit 1
fi

echo "ok   certificate-at-office (tampered/wrong-key/weakening artifacts refused; certified Amend takes office)"
