# Conformance tests (plan §5.3)

One file per normative statement of `docs/spec/`, named
`spec_<chapter>_<statement>_<topic>`. Each file's first comment line quotes the
statement it pins; a `//!` directive (see `charter test`) says when the expected
outcome is a diagnostic. Run with `charter test test/spec`; `tools/battery` does.

Files use the `.eflint` extension until the `.charter` extension moves from the
v0.3 grammar to this one (docs/spec/README.md). `include/` holds files the
`#include`/`#require` tests load.

Generated from one table by the session that wrote the chapters; edit the files
directly from now on.
