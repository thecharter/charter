#!/usr/bin/env bash
# Law 14 Gate (`law14-sentences-resolve`, D49): a sentence may not run ahead of its code.
# 1. Every command-line flag written in backticks in `docs/spec/`, `docs/targets.md`, or
#    `docs/claims.json` is a flag the binary parses (it occurs in `src/`).
# 2. Every code identifier written in backticks there (camelCase, a theorem name, or a
#    `Charter.`-qualified name) is defined or used in `src/` or `lib/`.
# 2a. Every path written in backticks in `docs/spec/` that begins with a top-level directory
#    of this repository exists (`D50`, `B37`). History is skipped by structure, not by date:
#    the `## Changelog` section of `docs/spec/README.md` and paragraphs that open with
#    `*Finding (` say what was true when they were written.
# 2b. The other direction (`D50`, `B38`): every `--flag` a command-line parser in `src/`
#    accepts is named in `docs/spec/018_toolchain_and_cli.md`. A flag that is parsed and
#    documented nowhere is how `--solver` and two ignored `verify` flags lived unseen.
# `docs/rfc.md` is a dated design record, marked as one in its header, and is not read.
# 3. No check that CI runs is followed by an unconditional pass: no command in
#    `.github/workflows/`, `tools/battery`, `tools/*-check`, or `test/gates/` ends in
#    "or true".
# Each of these would have gone red on the day `importQuintTrace` entered 017.4, `--emit-smt`
# fed a solver nobody read, and a CI step ran a fixture that did not exist. The gate first
# shows it can fail, on those three sentences.
set -u
cd "$(dirname "$0")/../.." || exit 2

python3 -I - <<'PY'
import pathlib, re, sys

root = pathlib.Path(".")
OR_TRUE = "|| " + "true"

# Names that belong to the proof checker, not to Charter, and are mentioned as such.
EXTERNAL = {
    "sorryAx": "the checker's own axiom; `Cli/Verify.lean` spells it in two halves so that "
               "`law10-trust-grep` does not read the refusal as a use",
}

def backticked(text):
    return re.findall(r"`([^`\n]+)`", text)

def flags_in(text):
    out = set()
    for t in backticked(text):
        out.update(re.findall(r"(?<![\w-])--[a-z][a-z0-9-]*", t))
    return out

def idents_in(text):
    out = set()
    for t in backticked(text):
        if not re.fullmatch(r"[A-Za-z_][\w.]*", t):
            continue
        last = t.split(".")[-1]
        camel = re.search(r"[a-z][A-Z]", last) is not None
        theorem = "_" in last and re.search(r"[A-Z]", last) is not None
        if camel or theorem or t.startswith("Charter."):
            out.add(t)
    return out

def unresolved_flags(flags, src):
    return sorted(f for f in flags if f not in src)

def unresolved_idents(idents, code):
    bad = []
    for i in sorted(idents):
        last = i.split(".")[-1]
        if last in EXTERNAL:
            continue
        if not re.search(r"(?<![\w])" + re.escape(last) + r"(?![\w])", code):
            bad.append(i)
    return bad

TOP_DIRS = sorted(p.name for p in root.iterdir() if p.is_dir() and not p.name.startswith(".")) + [".github"]

def without_history(name, text):
    """The text with its history removed: README's Changelog section, `*Finding (` paragraphs."""
    out, in_changelog = [], False
    for para in text.split("\n\n"):
        first = para.lstrip().split("\n", 1)[0]
        if first.startswith("## "):
            in_changelog = name == "README.md" and first.strip() == "## Changelog"
        if in_changelog or para.lstrip().startswith("*Finding ("):
            continue
        out.append(para)
    return "\n\n".join(out)

def paths_in(text):
    out = set()
    for t in backticked(text):
        m = re.fullmatch(r"([A-Za-z.][\w.-]*)/[\w./-]*", t)
        if m and m.group(1) in TOP_DIRS:
            out.add(t)
    return out

def missing_paths(paths):
    return sorted(p for p in paths if not (root / p).exists())

def parsed_flags(lean_text):
    """Flags a parser matches on: a string literal that is exactly one flag."""
    return set(re.findall(r'"(--[a-z][a-z0-9-]*)"', lean_text))

def undocumented(flags, chapter):
    return sorted(f for f in flags if not re.search(r"(?<![\w-])" + re.escape(f) + r"(?![\w-])", chapter))

def or_true_lines(path, text):
    return [f"{path}:{n}" for n, line in enumerate(text.splitlines(), 1)
            if OR_TRUE in line and not line.lstrip().startswith("#")]

src = "\n".join(p.read_text(encoding="utf-8") for p in sorted((root / "src").rglob("*.lean")))
code = src + "\n" + "\n".join(
    p.read_text(encoding="utf-8") for p in sorted((root / "lib").rglob("*")) if p.is_file() and p.suffix in (".lean", ".charter"))

# 0. The gate can fail: the three sentences it exists for are caught.
probe = "traces (`importQuintTrace`) are certified; `--emit-smt <path>` feeds the solver"
if unresolved_idents(idents_in(probe), code) != ["importQuintTrace"]:
    print("FAIL law14-sentences-resolve: self-check: an identifier with no definition was not caught")
    sys.exit(1)
if unresolved_flags(flags_in(probe), src) != ["--emit-smt"]:
    print("FAIL law14-sentences-resolve: self-check: a flag the binary does not parse was not caught")
    sys.exit(1)
if or_true_lines("probe", "charter verify missing.charter " + OR_TRUE) != ["probe:1"]:
    print("FAIL law14-sentences-resolve: self-check: an unconditional pass was not caught")
    sys.exit(1)

hist = "## Changelog\n\n- then `tools/no-such-thing` existed\n\n## Chapters\n\nnow `tools/no-such-thing` and `tools/battery`\n\n*Finding (2026-10-25):* `test/no-such-dir/` was slow"
if missing_paths(paths_in(without_history("README.md", hist))) != ["tools/no-such-thing"]:
    print("FAIL law14-sentences-resolve: self-check: a path that names nothing was not caught exactly once, outside history")
    sys.exit(1)
if undocumented(parsed_flags('| "--solver" :: s :: rest, o => x\n| "--depth" :: n'), "takes `--depth <N>` and `--solver-kind`") != ["--solver"]:
    print("FAIL law14-sentences-resolve: self-check: a parsed flag the CLI chapter does not name was not caught")
    sys.exit(1)

docs = sorted((root / "docs" / "spec").glob("*.md")) + [root / "docs" / "targets.md", root / "docs" / "claims.json"]
problems = []
n_flags = n_idents = n_paths = 0
for d in docs:
    text = d.read_text(encoding="utf-8")
    fl, ids = flags_in(text), idents_in(text)
    n_flags += len(fl); n_idents += len(ids)
    for f in unresolved_flags(fl, src):
        problems.append(f"{d}: flag `{f}` is not parsed anywhere in src/")
    for i in unresolved_idents(ids, code):
        problems.append(f"{d}: identifier `{i}` is not defined or used in src/ or lib/")
    if d.parent.name == "spec":
        ps = paths_in(without_history(d.name, text))
        n_paths += len(ps)
        for p in missing_paths(ps):
            problems.append(f"{d}: path `{p}` names nothing in the tree")

cli_chapter = (root / "docs" / "spec" / "018_toolchain_and_cli.md").read_text(encoding="utf-8")
accepted = parsed_flags(src)
for f in undocumented(accepted, cli_chapter):
    problems.append(f"src/: flag `{f}` is accepted by a parser and is not named in docs/spec/018_toolchain_and_cli.md")

ci = sorted((root / ".github" / "workflows").glob("*")) + [root / "tools" / "battery"] + \
     sorted((root / "tools").glob("*-check")) + sorted((root / "test" / "gates").glob("*.sh"))
n_ci = 0
for p in ci:
    if not p.is_file():
        continue
    n_ci += 1
    for loc in or_true_lines(p, p.read_text(encoding="utf-8")):
        problems.append(f"{loc}: a command CI runs ends in an unconditional pass; test its status or its output instead")

if problems:
    print("FAIL law14-sentences-resolve:")
    for pr in problems:
        print("     " + pr)
    sys.exit(1)
print(f"ok   law14-sentences-resolve ({n_flags} flags, {n_idents} identifiers and {n_paths} paths in {len(docs)} documents resolve; {len(accepted)} parsed flags are named in 018; {n_ci} CI scripts have no unconditional pass)")
PY
