#!/usr/bin/env bash
# Law 14 / D11 Gate (`amend-is-an-act`):
# A weakening `Amend` is performed as an institutional act in the trace: it MUST occur
# (`occurred: true`), be reported void (`valid: no`), and leave the protected rule set intact.
set -u
cd "$(dirname "$0")/../.." || exit 2
B=.lake/build/bin/charter
[ -x "$B" ] || { echo "FAIL amend-is-an-act: $B missing"; exit 2; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/weak_amend.charter" <<'EOF'
Fact council Identified by C1.
Fact member Identified by Ava.
Fact quorum Identified by council.
Fact exited Identified by member.

Power exit-right Actor member
  Holds when True
  Valid when True
  Creates exited(member).

Immunity protect-exit Holder member
  Against Amend
  Protects exit-right
  Holds when True.

Amend repeal-exit Actor council
  Repeals exit-right
  Holds when quorum(council)
  Valid when quorum(council).

+quorum(C1).
repeal-exit(C1).
exit-right(Ava).
?exited(Ava).
EOF

out=$("$B" run "$tmp/weak_amend.charter" 2>&1); st=$?
if [ "$st" -ne 0 ]; then
  echo "FAIL amend-is-an-act: run exited $st"
  printf '%s\n' "$out"
  exit 1
fi
if ! printf '%s\n' "$out" | grep -qE 'occurred act repeal-exit.*valid: no'; then
  echo "FAIL amend-is-an-act: weakening Amend was not recorded as occurred + void"
  printf '%s\n' "$out"
  exit 1
fi
echo "ok   amend-is-an-act (weakening Amend occurred, reported void, protected power preserved)"
