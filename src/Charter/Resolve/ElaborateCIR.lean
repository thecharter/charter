import Charter.Resolve.Static
import Charter.Core.Derivation
import Charter.Artifact.Hash

/-!
# Charter.Resolve.ElaborateCIR — Canonical Institutional IR (`CIR`) & Well-Formedness (`D18`)

Defines the decidable structural well-formedness predicate `Spec.WellFormed` (`checkWellFormed`)
over `Core.Spec`, segments resolved phrase streams into immutable `LawVersion` epochs
(`CIR.Epoch` / `CIR.Program`), and proves that every elaborated epoch is `WellFormed`.
-/

namespace Charter

namespace CIR

/-- One immutable law-version epoch of an elaborated program (`D18`). -/
structure Epoch where
  version    : Nat
  spec       : Spec
  strata     : List (List DomId)
  specSha256 : String
  phrases    : List CPhrase
  deriving Repr

/-- Complete elaborated program: ordered `LawVersion` epochs and accumulated warnings. -/
structure Program where
  epochs   : List Epoch
  warnings : List Diagnostic
  deriving Repr

def specDigest (s : Spec) : String :=
  Artifact.sha256String (reprStr s)

def validateEpochSpec (s : Spec) : Except (List Diagnostic) (List (List DomId)) :=
  match Stratify.strata s with
  | .error cyc =>
    .error [Diagnostic.error "CHR020"
      s!"derivation is not stratifiable: {", ".intercalate cyc} depend on their own absence (through Not, Forall, or an aggregate)"]
  | .ok st =>
    if s.checkWellFormed then .ok st
    else .error [Diagnostic.error "CHR010" "resolved specification failed CIR well-formedness check"]

def mkValidatedEpoch (ver : Nat) (s : Spec) (ps : List CPhrase) : Except (List Diagnostic) Epoch :=
  match validateEpochSpec s with
  | .error ds => .error ds
  | .ok st => .ok { version := ver, spec := s, strata := st, specSha256 := specDigest s, phrases := ps }

theorem mkValidatedEpoch_wellFormed {ver : Nat} {s : Spec} {ps : List CPhrase} {ep : Epoch}
    (h : mkValidatedEpoch ver s ps = .ok ep) : ep.spec.WellFormed := by
  unfold mkValidatedEpoch validateEpochSpec at h
  cases hs : Stratify.strata s with
  | error _ => rw [hs] at h; cases h
  | ok st =>
    rw [hs] at h
    dsimp only at h
    by_cases hwf : s.checkWellFormed = true
    · rw [if_pos hwf] at h
      injection h with heq
      rw [← heq]
      exact hwf
    · have hwfF : s.checkWellFormed = false := Bool.eq_false_iff.mpr hwf
      rw [hwfF] at h
      cases h

def elaborateLoop : Nat → Spec → List CPhrase → List Phrase → List Diagnostic →
    Except (List Diagnostic) (List Epoch × List Diagnostic)
  | ver, curSpec, curPhrases, [], warns => do
    let ep ← mkValidatedEpoch ver curSpec curPhrases.reverse
    return ([ep], warns)
  | ver, curSpec, curPhrases, p :: rest, warns => do
    let (nextSpec, cp, ws) ← resolvePhrase curSpec p
    let warns := warns ++ ws
    match cp with
    | .onlyDecls _ =>
      if curPhrases.isEmpty then
        elaborateLoop ver nextSpec [] rest warns
      else
        let ep ← mkValidatedEpoch ver curSpec curPhrases.reverse
        let (tail, warns') ← elaborateLoop (ver + 1) nextSpec [] rest warns
        return (ep :: tail, warns')
    | _ =>
      elaborateLoop ver nextSpec (cp :: curPhrases) rest warns

/-- Elaborate parsed top-level `Phrase`s into validated `CIR` epochs. -/
def elaboratePhrases (phrases : List Phrase) : Except (List Diagnostic) Program := do
  let (epochs, warnings) ← elaborateLoop 0 emptySpec [] phrases []
  return { epochs, warnings }

theorem elaborateLoop_wellFormed :
    ∀ (ps : List Phrase) (ver : Nat) (curSpec : Spec) (curPhrases : List CPhrase)
      (warns : List Diagnostic) (eps : List Epoch) (warns' : List Diagnostic),
      elaborateLoop ver curSpec curPhrases ps warns = .ok (eps, warns') →
      ∀ ep ∈ eps, ep.spec.WellFormed
  | [], ver, curSpec, curPhrases, warns, eps, warns', h => by
    unfold elaborateLoop at h
    cases hm : mkValidatedEpoch ver curSpec curPhrases.reverse with
    | error _ => rw [hm] at h; cases h
    | ok ep0 =>
      rw [hm] at h
      injection h with hpair
      injection hpair with heps _
      intro ep hep
      rw [← heps] at hep
      simp only [List.mem_singleton] at hep
      rw [hep]
      exact mkValidatedEpoch_wellFormed hm
  | p :: rest, ver, curSpec, curPhrases, warns, eps, warns', h => by
    unfold elaborateLoop at h
    cases hr : resolvePhrase curSpec p with
    | error _ => rw [hr] at h; cases h
    | ok triple =>
      rcases triple with ⟨nextSpec, cp, ws⟩
      rw [hr] at h
      dsimp only [Bind.bind, Except.bind] at h
      cases cp with
      | onlyDecls ds =>
        by_cases hemp : curPhrases.isEmpty = true
        · rw [if_pos hemp] at h
          exact elaborateLoop_wellFormed rest ver nextSpec [] (warns ++ ws) eps warns' h
        · rw [if_neg hemp] at h
          cases hm : mkValidatedEpoch ver curSpec curPhrases.reverse with
          | error _ => rw [hm] at h; cases h
          | ok ep0 =>
            rw [hm] at h
            dsimp only at h
            cases htail : elaborateLoop (ver + 1) nextSpec [] rest (warns ++ ws) with
            | error _ => rw [htail] at h; cases h
            | ok pair =>
              rcases pair with ⟨tail, w2⟩
              rw [htail] at h
              injection h with hpair
              injection hpair with heps _
              intro ep hep
              rw [← heps, List.mem_cons] at hep
              cases hep with
              | inl h0 =>
                rw [h0]
                exact mkValidatedEpoch_wellFormed hm
              | inr hmem =>
                exact elaborateLoop_wellFormed rest (ver + 1) nextSpec [] (warns ++ ws) tail w2 htail ep hmem
      | trigger _ _ | create _ _ | terminate _ _ | obfuscate _ _ | query _ | instQuery _ _ _
      | par _ | scenario _ _ | expect _ _ _ _ | setTime _ | tick | why _ _
      | submitEvidence _ _ _ _ | retractEvidence _ _ _ =>
        exact elaborateLoop_wellFormed rest ver nextSpec (_ :: curPhrases) (warns ++ ws) eps warns' h

/-- Every `CIR.Epoch` produced by `elaboratePhrases` has a `WellFormed` `Spec`. -/
theorem elaboratePhrases_epochs_wellFormed (ps : List Phrase) (prog : Program)
    (h : elaboratePhrases ps = .ok prog) :
    ∀ ep ∈ prog.epochs, ep.spec.WellFormed := by
  unfold elaboratePhrases at h
  cases hl : elaborateLoop 0 emptySpec [] ps [] with
  | error _ => rw [hl] at h; cases h
  | ok pair =>
    rcases pair with ⟨eps, ws⟩
    rw [hl] at h
    injection h with hp
    rw [← hp]
    exact elaborateLoop_wellFormed ps 0 emptySpec [] [] eps ws hl

end CIR

end Charter
