import Charter.Surface.Ast
import Charter.Core.Spec

/-!
# Charter.Resolve.AssuranceGates — Opt-In Static Assurance Gates

Enforces project-level static auditability and completeness checks (`--require-provenance`,
`--forbid-midstream-decls`, `--require-complete-explore`, `--deny-warnings`) without
altering the operational or declarative meaning of any Charter or eFLINT construct
(`docs/rfc.md` §3.6, §12.1; `docs/spec/` 012.10, 018.2).
-/

namespace Charter

structure AssuranceOpts where
  requireProvenance      : Bool := false
  forbidMidstreamDecls   : Bool := false
  requireCompleteExplore : Bool := false
  denyWarnings           : Bool := false
  deriving Repr, Inhabited

namespace AssuranceGates

/-- `CHR030` (`--forbid-midstream-decls`): reject top-level declaration blocks appearing
after any top-level execution, state-mutation, or query phrase. -/
def checkMidstreamDecls (items : List (String × Item)) : List Diagnostic :=
  let (_, diags) := items.foldl (fun (seenExec, acc) (file, it) =>
    match it.val with
    | .inl _ => (seenExec, acc)
    | .inr (.decls _) =>
      if seenExec then
        let d := (Diagnostic.error "CHR030"
          "declaration block appears after top-level execution or state phrases (--forbid-midstream-decls)"
          it.pos).withFile file
        (seenExec, acc ++ [d])
      else (seenExec, acc)
    | .inr (.scenario _ _ _) => (seenExec, acc)
    | .inr _ => (true, acc)) (false, [])
  diags

/-- `CHR029` (`--require-provenance`): require an authoritative readable `Document` and
`Clause` coverage whenever normative rules are declared (012.10, T08). -/
def checkProvenanceGate (file : String) (spec : Spec) (docLoaded : Option (Except String String)) : List Diagnostic :=
  if spec.ruleIds.isEmpty then []
  else if spec.document.isNone || spec.clauses.isEmpty then
    [(Diagnostic.error "CHR029"
      "normative rules declared without an authoritative `Document` and `Clause` coverage (--require-provenance)").withFile file]
  else match docLoaded with
    | some (.ok _) => []
    | some (.error e) =>
      [(Diagnostic.error "CHR029"
        s!"authoritative Document `{spec.document.getD ""}` could not be read ({e}) (--require-provenance)").withFile file]
    | none =>
      [(Diagnostic.error "CHR029"
        s!"authoritative Document `{spec.document.getD ""}` was not read (--require-provenance)").withFile file]

/-- `CHR031` (`--require-complete-explore`): require a positive exploration depth whenever
invariants are declared. -/
def checkCompleteExploreGate (file : String) (spec : Spec) (exploreDepth : Nat) : List Diagnostic :=
  if !spec.invariants.isEmpty && exploreDepth == 0 then
    [(Diagnostic.error "CHR031"
      s!"invariants declared ({", ".intercalate spec.invariants}) without a positive exploration depth; pass `--explore <depth>` or add `//! explore: <depth>` (--require-complete-explore)").withFile file]
  else []

end AssuranceGates

end Charter
