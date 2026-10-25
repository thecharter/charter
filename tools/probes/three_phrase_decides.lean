/-
The first kernel decision of a Charter program (spec 013.4). The three-phrase program
`Fact x Identified by A. +x(A). ?x(A).` is embedded as parsed items (the parser is never
run in the kernel: parsing this text there exceeds 180 s) and the evaluator's verdict is
decided by `decide +kernel`, which hands the closed term straight to the kernel.

Run only through the capped tool (AGENTS.md, "Kernel experiments run capped"):

    tools/kernel-probe tools/probes/three_phrase_decides.lean

Measured 2026-10-24 on the maintainer machine: `kernel-probe: ok in 0 s` (under a second,
imports already built). The same theorem with plain `by decide` took about 200 s, and the
create phrase alone, with plain `by decide`, passed 6 GB of resident memory in 6 s and was
killed by the watchdog. The difference is the elaborator's own `Meta.whnf` evaluation of
the `Decidable` instance, which plain `decide` runs before the kernel sees the term; the
kernel itself decides the program instantly. `prove`'s generator therefore emits
`decide +kernel`.
-/
import Charter.Prove.Run
open Charter

def items : List Item := [
  ⟨⟨1,0⟩, "", .inr (.decls [.typeDecl "x" { kind := .fact {}, domain := .strings ["A"] }])⟩,
  ⟨⟨1,0⟩, "", .inr (.create [] (.app "x" (.pos [.stringLit "A"])))⟩,
  ⟨⟨1,0⟩, "", .inr (.query (.app "x" (.pos [.stringLit "A"])))⟩ ]

#eval (Prove.runItems items).ok

theorem three_phrase_decides : (Prove.runItems items).ok = true := by decide +kernel
