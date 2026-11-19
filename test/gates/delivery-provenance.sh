#!/usr/bin/env bash
# Law 8 / D46 Gate (`delivery-provenance`, spec 012.7):
# 1. a declared `Document` that cannot be read is `CHR053` and a non-zero exit in every
#    command that loads the program, and no summary line says `ok`;
# 2. `charter build` and `charter generate` refuse provenance coverage `partial` (`CHR054`);
# 3. an `illustrative` program is delivered and says so: in the signed manifest, on
#    `build`'s summary line, and in the text of every projection;
# 4. a `complete` program is stamped `complete`.
set -u
cd "$(dirname "$0")/../.." || exit 2
B=.lake/build/bin/charter
[ -x "$B" ] || { echo "FAIL delivery-provenance: $B missing"; exit 2; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail() { echo "FAIL delivery-provenance: $1"; exit 1; }

# 1. unreadable Document
cat > "$tmp/unreadable.charter" <<'EOF'
Document "no-such-document.md".
Fact member Identified by Ann.
Fact joined Identified by member.
Act join Actor member Holds when True Creates joined(member).
join(Ann).
EOF
for cmd in "check" "run" "test" "build" "generate --target prompt" "generate --target quint" "verify --depth 1" "explore --depth 1" "doc"; do
  # shellcheck disable=SC2086
  out=$("$B" $cmd "$tmp/unreadable.charter" 2>&1); st=$?
  [ "$st" -ne 0 ] || fail "\`charter $cmd\` exits 0 on a Document it cannot read"
  printf '%s\n' "$out" | grep -q 'CHR053' || fail "\`charter $cmd\` does not report CHR053: $out"
  printf '%s\n' "$out" | grep -qE '^ok ' && fail "\`charter $cmd\` prints an ok line over an unreadable Document"
done

# 2. partial coverage is not delivered
printf 'The member may join.\n' > "$tmp/rules.md"
cat > "$tmp/partial.charter" <<'EOF'
Document "rules.md".
Fact member Identified by Ann.
Fact joined Identified by member.
Act join Actor member Holds when True Creates joined(member).
EOF
for cmd in "build" "generate --target prompt" "generate --target solidity" "generate --target quint"; do
  # shellcheck disable=SC2086
  out=$("$B" $cmd "$tmp/partial.charter" 2>&1); st=$?
  [ "$st" -ne 0 ] || fail "\`charter $cmd\` delivers a program whose coverage is partial"
  printf '%s\n' "$out" | grep -q 'CHR054' || fail "\`charter $cmd\` does not report CHR054: $out"
done

# 3. illustrative is delivered and stamped
cat > "$tmp/illustrative.charter" <<'EOF'
Fact member Identified by Ann.
Fact joined Identified by member.
Act join Actor member Holds when True Creates joined(member).
EOF
out=$("$B" build "$tmp/illustrative.charter" -o "$tmp/i.artifact" 2>&1) || fail "build refuses an illustrative program: $out"
printf '%s\n' "$out" | grep -q 'provenance illustrative' || fail "build's summary line does not print the coverage: $out"
grep -q '"coverage": "illustrative"' "$tmp/i.artifact" || fail "the signed manifest does not record coverage illustrative"
for tgt in prompt solidity quint; do
  out=$("$B" generate --target "$tgt" "$tmp/illustrative.charter" 2>/dev/null) || fail "generate --target $tgt refuses an illustrative program"
  printf '%s\n' "$out" | grep -q 'Provenance (Law 8): illustrative' || fail "the $tgt projection is not stamped illustrative"
done
out=$("$B" generate --target prompt --out json "$tmp/illustrative.charter" 2>/dev/null)
printf '%s\n' "$out" | grep -q '"provenance": "illustrative"' || fail "the prompt JSON carries no provenance field"

# 4. complete is stamped complete
EX=Examples/Tenancy/tenancy.charter
out=$("$B" build "$EX" -o "$tmp/t.artifact" 2>&1) || fail "build refuses $EX: $out"
printf '%s\n' "$out" | grep -q 'provenance complete' || fail "build does not report $EX as complete: $out"
out=$("$B" generate --target prompt "$EX" 2>/dev/null) || fail "generate --target prompt refuses $EX"
printf '%s\n' "$out" | grep -q 'Provenance (Law 8): complete' || fail "the prompt projection of $EX is not stamped complete"

echo "ok   delivery-provenance (unreadable Document refused by 9 commands; partial not delivered; illustrative and complete stamped)"
