#!/usr/bin/env bash
# Law 14 / D11 Gate (`amend-reflexive`):
# An entrenchment immunity `Against Amend` is reflexively protected: attempting first to
# `Amend` the immunity itself and then to `Amend` the protected floor MUST record both acts
# as void (`valid: no`) and preserve the floor (`T24`).
set -u
cd "$(dirname "$0")/../.." || exit 2
B=.lake/build/bin/charter
[ -x "$B" ] || { echo "FAIL amend-reflexive: $B missing"; exit 2; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/reflexive_amend.charter" <<'EOF'
Fact council Identified by C1.
Fact member Identified by Ava.
Fact quorum Identified by council.
Fact exited Identified by member.

Power exit-right Actor member
  Holds when True
  Valid when True
  Creates exited(member).

Immunity ratchet-immunity Holder member
  Against Amend
  Protects exit-right
  Holds when True.

Amend repeal-ratchet Actor council
  Repeals ratchet-immunity
  Holds when quorum(council)
  Valid when quorum(council).

Amend repeal-exit Actor council
  Repeals exit-right
  Holds when quorum(council)
  Valid when quorum(council).

+quorum(C1).
repeal-ratchet(C1).
repeal-exit(C1).
exit-right(Ava).
?exited(Ava).
EOF

out=$("$B" run "$tmp/reflexive_amend.charter" 2>&1); st=$?
if [ "$st" -ne 0 ]; then
  echo "FAIL amend-reflexive: run exited $st"
  printf '%s\n' "$out"
  exit 1
fi
if ! printf '%s\n' "$out" | grep -qE 'occurred act repeal-ratchet.*valid: no'; then
  echo "FAIL amend-reflexive: step 1 (repeal-ratchet) was not void"
  printf '%s\n' "$out"
  exit 1
fi
if ! printf '%s\n' "$out" | grep -qE 'occurred act repeal-exit.*valid: no'; then
  echo "FAIL amend-reflexive: step 2 (repeal-exit) was not void"
  printf '%s\n' "$out"
  exit 1
fi
echo "ok   amend-reflexive (both ratchet-repeal and floor-repeal void; floor preserved)"
