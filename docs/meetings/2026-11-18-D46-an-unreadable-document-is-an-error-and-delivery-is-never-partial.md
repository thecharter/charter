# D46 — A declared `Document` that cannot be read is an error; `build` and `generate` deliver `complete` or `illustrative`, stamped, and never `partial`

**Laws:** 8, 10, 13, 14 (`docs/mission.md`). Brief `B34` (`2026-11-18-briefs-for-ruling.md`). Rewords spec `012.7`.
**Date:** 2026-11-18
**Status:** ruled (Eric, 2026-11-18): option A as predicted, sharpened so the classification travels with the output

## Context

`charter check` on a program whose `Document "x.md"` was missing printed `WARN … verbatim check skipped` and then `ok … coverage partial, 0 warning(s)`. `charter build` signed a bundle whose manifest said `partial` and did not print it. `charter generate` asked nothing about provenance. Spec `012.7` said an unreadable document "is a warning, not a failure, and the check is skipped", which is the silence `Law 8` and `AGENTS.md` ("No silent fallbacks") forbid: the program named its English and the tool did not check against it. An outside review of the repository raised the same point and asked for a flag (`--allow-ungrounded`) on every ungrounded build.

## Ruling

1. A declared `Document` that cannot be read, or whose content does not match its `SHA256` pin, is `CHR053`. It is raised where the program is loaded (`Charter.Cli.Load.checkDeclaredDocuments`), so every command reports it and exits non-zero: `check`, `run`, `test`, `build`, `generate`, `verify`, `explore`, `doc`, and the rest. Catala does the same for a law text it cannot find (`.reference/catala/compiler/surface/parser_driver.ml:443`).
2. `charter build` and `charter generate` refuse coverage `partial` (`CHR054`, printed after the failing checks). They accept `complete` and `illustrative`.
3. The classification travels with the output. `build` records it in the signed manifest (as before) and prints it on its summary line. `generate` writes `Provenance (Law 8): <classification>` into the text of the Solidity guard, the settlement contract, the Quint module, and the prompt briefing, adds a `provenance` field to every `--out json` wrapper and to the prompt schema, and prints it on its summary line. An artifact with no English behind it says so wherever it is read; that meets the reviewer's concern without a flag on every fixture that claims no document (`Law 13`).
4. `check`'s summary counted provenance checks it had printed as `WARN` as zero warnings. They are counted. Since item 1 no provenance check warns: the verbatim check on an unreadable document is a failed check.
5. `--require-provenance` keeps its meaning (`012.10`): it also refuses `illustrative`.

## Words (`012.7`, Eric's)

> A declared `Document` that cannot be read, or whose `SHA256` does not match, is an error (`CHRxxx`) in every command that resolves the program. A program that declares no `Document` is `illustrative` (012.10); `build` and `generate` accept it and stamp every output with that classification, and refuse `partial`.

`CHRxxx` is `CHR053`. The spec text also names `CHR054` for the refusal; that parenthesis is the implementer's and is Eric's to strike.

## Alternatives weighed

- **B, a flag for every ungrounded delivery.** Ceremony on every fixture that claims no document, for a state that is already named (`illustrative`). Dropped by the ruling; item 3 carries its purpose.
- **C, print the coverage and leave `012.7`.** Leaves the skipped check.

## Evidence

- `test/gates/delivery-provenance.sh`: nine commands refuse an unreadable `Document` with `CHR053` and print no `ok` line; `build` and three `generate` targets refuse `partial` with `CHR054`; `illustrative` and `complete` are stamped in the manifest, the summary line, and three projections.
- `test/spec/spec_012_7b_unreadable_document_is_an_error.charter` (new); `spec_012_9b_stale_sha256_drift.charter` now also expects `CHR053`.
- `tools/battery` with `CHARTER_REQUIRE_EXTERNAL_TOOLS=1`: PASS. No in-tree example, fixture, benchmark, or UAT program had to change: none was delivered `partial`.

## Cost accepted

- `--target abi` emits an Ethereum JSON ABI, a bare array with no field for a stamp. Its classification is on the summary line, on a `note` line to stderr when the ABI goes to stdout, and in the `--out json` wrapper. The text of the ABI itself does not carry it.
- A pinned document that does not match is reported twice by `check` and `test`: `CHR053` from the loader and the `STALE` provenance check. The check is kept so the language server, which resolves without the loader, still shows it.
- A program with `Clause`s and no `Document`, or a `Document` and no `Clause`, is `partial` and is not delivered until it is one or the other.

## Reopens if

A target gains a consumer that needs the classification inside an ABI (a metadata sidecar would be a new output, `017.1`), or a class of program appears for which `partial` delivery is wanted on purpose.
