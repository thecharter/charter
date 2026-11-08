#!/usr/bin/env bash
# Gate G1.1 (`spec-inventory` & AST formatter round-trip):
# 1. Every CHR diagnostic code emitted in `src/Charter/` is documented in `docs/spec/diagnostics.md`.
# 2. Every word keyword and claim keyword in `src/Charter/Surface/Lexer.lean` is documented in `docs/spec/020_grammar.md`.
# 3. `charter fmt --stdout` succeeds with verified AST round-trip across all `lib/*.charter`,
#    all `Examples/**/*.charter`, and every parseable file in the 196-file eFLINT corpus, and is idempotent.
set -u
cd "$(dirname "$0")/../.." || exit 2
B=".lake/build/bin/charter"
if [ ! -x "$B" ]; then echo "FAIL spec-inventory: $B is not built"; exit 2; fi

python3 -I - <<'PY'
import pathlib, re, subprocess, sys

root = pathlib.Path(".")
diag_doc = (root / "docs" / "spec" / "diagnostics.md").read_text(encoding="utf-8")
doc_codes = set(re.findall(r"\bCHR\d{3}\b", diag_doc))

src_codes = set()
for p in (root / "src" / "Charter").rglob("*.lean"):
    src_codes.update(re.findall(r'"(CHR\d{3})"', p.read_text(encoding="utf-8")))

missing_codes = sorted(src_codes - doc_codes)
if missing_codes:
    print(f"FAIL spec-inventory: undocumented diagnostic codes in src/Charter/: {missing_codes}")
    sys.exit(1)

lexer_txt = (root / "src" / "Charter" / "Surface" / "Lexer.lean").read_text(encoding="utf-8")
grammar_doc = (root / "docs" / "spec" / "020_grammar.md").read_text(encoding="utf-8")

for block_name in ("wordKeywords", "claimKeywords"):
    m = re.search(rf"def {block_name}\s*:\s*List String\s*:=\s*\[(.*?)\]", lexer_txt, re.S)
    if not m:
        print(f"FAIL spec-inventory: could not locate {block_name} in Lexer.lean")
        sys.exit(1)
    kws = re.findall(r'"([^"]+)"', m.group(1))
    missing_kws = [k for k in kws if f"`{k}`" not in grammar_doc and f"'{k}'" not in grammar_doc]
    if missing_kws:
        print(f"FAIL spec-inventory: keywords in {block_name} missing from 020_grammar.md: {missing_kws}")
        sys.exit(1)

targets = sorted(list((root / "lib").glob("*.charter")) + list((root / "Examples").rglob("*.charter")) +
                 list((root / "test" / "eflint-corpus" / "tests").rglob("*.eflint")) +
                 list((root / "test" / "eflint-corpus" / "examples").rglob("*.eflint")))

bin_path = str(root / ".lake" / "build" / "bin" / "charter")
checked = 0
for f in targets:
    r1 = subprocess.run([bin_path, "fmt", "--stdout", str(f)], capture_output=True, text=True)
    if r1.returncode != 0:
        print(f"FAIL spec-inventory: charter fmt round-trip failed on {f}:\n{r1.stderr}")
        sys.exit(1)
    # Verify idempotence: formatting the formatted output yields byte-identical output
    tmp = root / "out" / "_fmt_idemp_check.charter"
    tmp.parent.mkdir(parents=True, exist_ok=True)
    tmp.write_text(r1.stdout, encoding="utf-8")
    r2 = subprocess.run([bin_path, "fmt", "--stdout", str(tmp)], capture_output=True, text=True)
    tmp.unlink(missing_ok=True)
    if r2.returncode != 0 or r2.stdout != r1.stdout:
        print(f"FAIL spec-inventory: charter fmt is not idempotent on {f}")
        sys.exit(1)
    checked += 1

# Verify `charter approve --lock` + rule-drift invalidation (`D34`, `#23`, `#32`, `#35`)
import tempfile, shutil
tmp_dir = pathlib.Path(tempfile.mkdtemp())
try:
    shutil.copy(root / "test" / "spec" / "include" / "byref_doc.md", tmp_dir / "doc.md")
    lf = tmp_dir / "lock_spec.charter"
    lf.write_text('//! require-provenance\nDocument "doc.md"\nFact person Identified by Anna\nAct pay-rent Actor person Holds when True\nClause 1.1 Definition\nClause 1.2/1 => pay-rent\nClause 1.2/2\nClause 1.3\n', encoding="utf-8")
    ra = subprocess.run([bin_path, "approve", "--lock", str(lf)], capture_output=True, text=True)
    rc = subprocess.run([bin_path, "check", "--require-provenance", "--deny-warnings", str(lf)], capture_output=True, text=True)
    if ra.returncode != 0 or rc.returncode != 0:
        print(f"FAIL spec-inventory: charter approve --lock check failed:\n{ra.stderr}\n{rc.stdout}\n{rc.stderr}")
        sys.exit(1)
    lf.write_text(lf.read_text(encoding="utf-8").replace("Holds when True", "Holds when False"), encoding="utf-8")
    rd = subprocess.run([bin_path, "check", "--require-provenance", str(lf)], capture_output=True, text=True)
    if rd.returncode == 0 or "STALE 1.2/1" not in (rd.stdout + rd.stderr):
        print(f"FAIL spec-inventory: rule-drift STALE detection failed:\n{rd.stdout}\n{rd.stderr}")
        sys.exit(1)
finally:
    shutil.rmtree(tmp_dir, ignore_errors=True)

print(f"ok   spec-inventory ({len(src_codes)} CHR codes, all lexer keywords, {checked} AST round-trips + idempotence, lockfile rule-drift check)")
PY
