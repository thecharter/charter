#!/usr/bin/env bash
# Law 14 / §3a Gate (`operator-blind`, G4.1):
# 1. Verifies the transitive Lean import closure of `src/Server.lean` touches ZERO modules
#    under `Charter.Surface.*`, `Charter.Resolve.*`, or `Charter.Prove.*`.
# 2. Scans the compiled `.lake/build/bin/charter-server` binary symbol table (`nm`) to confirm
#    zero `Charter_Surface_`, `Charter_Resolve_`, or `Charter_Prove_` symbols are linked.
set -u
cd "$(dirname "$0")/../.." || exit 2
SB=.lake/build/bin/charter-server
[ -x "$SB" ] || { echo "FAIL operator-blind: $SB is not built"; exit 2; }

python3 -I - <<'PY'
import pathlib, re, subprocess, sys

root = pathlib.Path(".")
src = root / "src"

def mod_to_path(mod: str) -> pathlib.Path:
    return src / pathlib.Path(*mod.split(".")).with_suffix(".lean")

visited = set()
stack = ["Server"]
forbidden_prefixes = ("Charter.Surface.", "Charter.Resolve.", "Charter.Prove.")

while stack:
    m = stack.pop()
    if m in visited:
        continue
    visited.add(m)
    for bad in forbidden_prefixes:
        if m.startswith(bad):
            print(f"FAIL operator-blind: Server transitively imports forbidden module `{m}`")
            sys.exit(1)
    fp = mod_to_path(m)
    if not fp.exists():
        continue
    for line in fp.read_text(encoding="utf-8").splitlines():
        mm = re.match(r"^\s*import\s+([A-Za-z0-9_.]+)", line)
        if mm:
            imp = mm.group(1)
            if imp == "Server" or imp.startswith("Charter."):
                stack.append(imp)

nm_out = subprocess.run(["nm", str(root / ".lake" / "build" / "bin" / "charter-server")],
                        capture_output=True, text=True)
if nm_out.returncode == 0:
    bad_syms = [ln for ln in nm_out.stdout.splitlines()
                if re.search(r"Charter_(Surface|Resolve|Prove)_", ln)]
    if bad_syms:
        print("FAIL operator-blind: forbidden compiler symbols linked in charter-server:")
        for s in bad_syms[:10]:
            print("  " + s)
        sys.exit(1)

print(f"ok   operator-blind ({len(visited)} transitive Server modules checked, zero Surface/Resolve/Prove symbols)")
PY
