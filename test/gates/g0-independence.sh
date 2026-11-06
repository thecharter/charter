#!/usr/bin/env bash
# Gate G0-INDEPENDENCE & D10 (RFC §0.3, Mission Laws 12–14):
# 1. No linked application companions (`import Examples`, `Examples.lean`, or `.lean` shadow models under `Examples/`).
# 2. No superseded v0.3 flat-grammar or `charter_*` macro second-spelling modules (`Law 13`).
# 3. `charter` executes cleanly in an isolated directory with stripped HOME and zero external repos.
set -u
cd "$(dirname "$0")/../.." || exit 2
ROOT=$(pwd)
B="$ROOT/.lake/build/bin/charter"
if [ ! -x "$B" ]; then echo "FAIL g0-independence: $B is not built"; exit 2; fi

if [ -e Examples.lean ] || [ -d Examples/SovereignAgency ]; then
  echo "FAIL g0-independence: Phase-0 application companion still present in tree"
  exit 1
fi

lean_examples=$(find Examples -name '*.lean' 2>/dev/null)
if [ -n "$lean_examples" ]; then
  echo "$lean_examples"
  echo "FAIL g0-independence: Lean shadow models found under Examples/ (violates D10)"
  exit 1
fi

for legacy in src/Charter/Surface/Dsl.lean src/Charter/Surface/Lower.lean src/Charter/Surface/Unlower.lean src/Charter/Surface/Syntax.lean src/Charter/Tooling/Cli.lean; do
  if [ -e "$legacy" ]; then
    echo "FAIL g0-independence: legacy second-spelling file still present: $legacy"
    exit 1
  fi
done

if grep -q "Examples" lakefile.toml src/Main.lean; then
  echo "FAIL g0-independence: lakefile.toml or src/Main.lean still references Examples"
  exit 1
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cp Examples/ServiceEscrow/service-escrow.md Examples/ServiceEscrow/service-escrow.charter "$tmp/"
(
  cd "$tmp" || exit 1
  HOME="$tmp" "$B" check service-escrow.charter >/dev/null &&
  HOME="$tmp" "$B" test service-escrow.charter >/dev/null
) || {
  echo "FAIL g0-independence: isolated execution outside repository failed"
  exit 1
}

echo "ok   g0-independence (standalone binary, zero shadow models, isolated execution)"
