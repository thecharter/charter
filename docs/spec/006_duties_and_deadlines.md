# 006 — Duties and deadlines

**Status:** draft (2026-10-23). Meaning fixed by D2, D7, and D12; wording awaits Eric. Implementation: compliant, including 6.7 (`Due within`).

**6.1 Duty instances.** `Duty d Holder h Claimant c [Related to …]` declares a type whose instances have a holder, a claimant, and the related objects, created and terminated like any fact (by `+`/`-` or by effects). `test/spec/spec_006_1_duty_instance.eflint`

**6.2 Violation.** A duty instance is *violated* when it holds and one of its `Violated when` conditions holds, the duty's components bound to the instance. Violation is a fact of the state (Law 3): `Violated(d(…))` answers it at any time. `test/spec/spec_006_2_violated_when.eflint`, `spec_006_5_violated_needs_holding.eflint`

**6.3 `Enforced by`.** `Enforced by a` adds the condition "`a` is enabled" to `Violated when`, with the duty's components bound. `test/spec/spec_006_3_enforced_by.eflint`

**6.4 `Created by`, `Terminated by`.** `Created by a` adds `Creates d()` to the act `a`; `Terminated by a` adds `Terminates d()` to `a` and makes `a` hold while `d()` holds (so the terminating act is enabled exactly while the duty exists). The duty's components are bound from the act's. `test/spec/spec_006_4_terminated_by_created_by.eflint`

**6.5 Reporting (D12).** After each phrase a duty violation is reported once, for duties violated now that were not violated after the previous phrase. Invariant violations (004.9) and disabled-act violations (005.2) are reported for the phrase that produced them.

**6.6 Findings.** A finding is an institutional act whose effect is the breached duty's declared remedies; the link from violation to finding is an assumption a program states, never a theorem the language supplies (Law 3). Nothing in the eFLINT core names remedies; Phase 2's `Immunity` and Phase 3's protocol rewrite do.

**6.7 Deadlines (D7).** `Due within d` on a duty is the violation condition `Held(d()) For d`: the duty is violated once it has been held for the duration `d` without being terminated; a condition over the stamp, never a lapse event (Law 7, 009.3). `test/spec/spec_006_7_due_within.eflint`
