# Gates (Law 14)

One program per law, each written to fail if the law is quietly lost (plan §5.5).
`tools/battery` runs every `*.sh` here. A gate is a shell script when the check
is a grep or a run of the binary, and a `.charter` fixture under the law's number
once the fixture format lands.

| Law | Gate | What fails it |
|---|---|---|
| 8 | `delivery-provenance.sh` | a command that exits 0 or prints `ok` over a declared `Document` it cannot read; `build` or `generate` delivering coverage `partial`; a delivered output that does not carry its classification (`D46`) |
| 14 | `law14-sentences-resolve.sh` | a backticked flag in `docs/spec/`, `docs/targets.md`, or `docs/claims.json` that the binary does not parse; a backticked code identifier there with no definition in `src/` or `lib/`; a command in CI's scripts that ends in an unconditional pass (`D49`) |
| 10 | `law10-trust-grep.sh` | `sorry`, `native_decide`, or `axiom` anywhere in `src/Charter/`, `Examples/`, `src/Main.lean`, `src/Charter.lean`, `Examples.lean` |
| 11 | `law11-no-engine-in-output.sh` | any author-visible output of the binary (`help`, `check`, `verify`, `sim`, `dsl`, `views`, an unknown command, a missing file, a file that does not parse) naming the engine: `lean`, `lake`, `olean`, `tactic`, `sorry` |
| 13 | `law13-leak-grep.sh` | the language layer `src/Charter/` naming an example program (`sovereign`, `psa`, `commons`) |

Gates still to write (plan §5.5), in the order the laws they test become
expressible in `.charter`: Laws 1–9 and 12 (the corpus run, `tools/battery`
step 6), the D10 gates `goal1-no-shadow-model` and `psa-adversarial-tests`, and
the D11 gates `amend-is-an-act`, `amend-reflexive`, `extend-never-at-runtime`.
