#!/usr/bin/env bash
# Gate for WP-0 / Law 10 / Law 14 (`docs/claims.json` & truthful README scope):
# 1. Every entry in `docs/claims.json` has valid assurance/scope tags and its artifact exists.
# 2. Every `proved` entry names an actual `theorem <symbol>` in that `.lean` file.
# 3. `README.md` contains no unqualified "formally verified compiler" overclaim.
set -u
cd "$(dirname "$0")/../.." || exit 2

python3 -I - <<'PY'
import json, pathlib, re, sys

root = pathlib.Path(".")
claims_path = root / "docs" / "claims.json"
if not claims_path.is_file():
    print("FAIL claims-backed: docs/claims.json missing")
    sys.exit(1)

data = json.loads(claims_path.read_text(encoding="utf-8"))
claims = data.get("claims", [])
if not claims:
    print("FAIL claims-backed: docs/claims.json has no claims")
    sys.exit(1)

valid_tags = {"proved", "decided", "checked", "assumed"}
valid_scopes = {"live-evaluator", "idealized-core-model", "concrete-trace", "bounded-exhaustive"}
seen_ids = set()

for c in claims:
    cid = c["id"]
    if cid in seen_ids:
        print(f"FAIL claims-backed: duplicate claim id {cid}")
        sys.exit(1)
    seen_ids.add(cid)
    tag = c["assurance"]
    scope = c["scope"]
    if tag not in valid_tags:
        print(f"FAIL claims-backed: {cid} has invalid assurance tag {tag!r} (Law 10)")
        sys.exit(1)
    if scope not in valid_scopes:
        print(f"FAIL claims-backed: {cid} has invalid scope {scope!r}")
        sys.exit(1)
    art = root / c["artifact"]
    if not art.exists():
        print(f"FAIL claims-backed: {cid} artifact missing: {c['artifact']}")
        sys.exit(1)
    sym = c["symbol"]
    if tag == "proved":
        txt = art.read_text(encoding="utf-8")
        pat = re.compile(r"\btheorem\s+" + re.escape(sym) + r"\b")
        if not pat.search(txt):
            print(f"FAIL claims-backed: {cid} theorem `{sym}` not found in {c['artifact']}")
            sys.exit(1)
    else:
        sym_path = root / sym
        if not sym_path.exists():
            print(f"FAIL claims-backed: {cid} symbol/gate path `{sym}` missing")
            sys.exit(1)

readme = (root / "README.md").read_text(encoding="utf-8")
if re.search(r"formally verified compiler", readme, re.IGNORECASE):
    print("FAIL claims-backed: README.md contains unqualified 'formally verified compiler' phrase")
    sys.exit(1)

print(f"ok   claims-backed ({len(claims)} claims verified against theorems/gates)")
PY
