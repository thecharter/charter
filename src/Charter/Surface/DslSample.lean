import Charter.Core.Semantics
import Charter.Surface.Lower

/-!
# Charter.Surface.DslSample — A Kernel-Decided Toy `.charter` Program

A small residential-tenancy charter, unrelated to any shipped example, embedded as
text and pushed through the whole pipeline inside the kernel: tokenize, parse,
validate, print, re-parse, lower, and evaluate a scenario. These theorems are the
language's own regression suite for the DSL; every `.charter` program a user writes
goes through exactly the same functions.
-/

namespace Charter.Dsl.Sample

open Charter Charter.Dsl

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sampleText : String := r#"-- A toy residential tenancy charter (test fixture; not a shipped example)
charter tenancy "Residential Tenancy"
document "tenancy.md"
default actor tenant

roles tenant, landlord, tribunal
acts evict, giveNotice, endTenancy, postDeposit, findUnlawfulEviction
facts leased, noticeGiven, depositPosted, initiator(role), unlawfulEvictionEstablished

params
  noticeWindow = 10
  bondDeadline = 5

regime "short notice"
  noticeWindow = 3

init leased

clause TEN.1 approved 0
  norm "No party may evict a leased tenant" => D.NO_EVICT
  commentary "; the tribunal may find an eviction unlawful."

clause TEN.2
  norm "A landlord may end a tenancy only after a notice window" => D.NOTICE, P.GIVE_NOTICE
  norm " and must post a deposit" => D.DEPOSIT
  commentary "."

duty D.NO_EVICT
  from TEN.1 "No party may evict a leased tenant"
  bearer anyone
  beneficiary only tenant
  active holds leased
  forbid act evict
  breach by P.FIND
  remedies unlawfulEvictionEstablished

duty D.NOTICE
  from TEN.2 "A landlord may end a tenancy only after a notice window"
  bearer only landlord
  beneficiary only tenant
  active holds leased
  forbid act endTenancy
  except when heldFor noticeGiven noticeWindow

duty D.DEPOSIT
  from TEN.2 "and must post a deposit"
  bearer only landlord
  beneficiary only tenant
  active holds leased
  require act postDeposit within bondDeadline

power P.GIVE_NOTICE
  from TEN.2 "only after a notice window"
  holder only landlord
  trigger act giveNotice
  valid holds leased
  adds noticeGiven
  adds initiator(landlord) to landlord

power P.FIND
  from TEN.1 commentary "the tribunal may find an eviction unlawful" meaning P.FIND, D.NO_EVICT
  holder only tribunal
  trigger act findUnlawfulEviction
  valid holds leased and not holds unlawfulEvictionEstablished
  establishes breach of D.NO_EVICT

immunity I.TENANT
  from TEN.1 "No party may evict a leased tenant"
  holder only tenant
  against P.FIND
  active holds depositPosted
"#

def parsedOk {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

def sampleDoc : Doc :=
  match parseCharterText sampleText with
  | .ok d => d
  | .error _ => {}

theorem sample_parses : parsedOk (parseCharterText sampleText) = true := by decide +kernel

theorem sample_valid : validate sampleDoc = [] := by decide +kernel

theorem sample_counts :
    (sampleDoc.roles.length == 3 && sampleDoc.clauses.length == 2 && sampleDoc.duties.length == 3 &&
     sampleDoc.powers.length == 2 && sampleDoc.immunities.length == 1 && sampleDoc.regimes.length == 1) = true := by
  decide +kernel

/-- Printing and re-parsing is the identity on the sample. -/
theorem sample_render_roundtrip :
    (match parseCharterText (render sampleDoc) with
     | .ok d => d == sampleDoc
     | .error _ => false) = true := by
  decide +kernel

def sample : Lowered := lower sampleDoc

theorem sample_lowered_wellFormed : sample.law.wellFormed = true := by decide +kernel

theorem sample_english_covered : (sample.clauses.all Clause.covered) = true := by decide +kernel

theorem sample_norms_interpreted : (sample.clauses.all Clause.normsInterpreted) = true := by decide +kernel

theorem sample_reverse_provenance :
    reverseProvenanceWith sample.clauses sample.law.spans (sample.law.dutyIds ++ sample.law.powerIds) = true := by
  decide +kernel

/-- Parameters are substituted: the regime shortens the notice window to 3. -/
theorem sample_regime_substitutes :
    (match (lowerLaw sampleDoc (sampleDoc.regimeEnv ⟨"short notice", [("noticeWindow", 3)]⟩)).duties[1]? with
     | some d => d.unlessCond == .heldFor ⟨"noticeGiven", none⟩ 3
     | none => false) = true := by
  decide +kernel

/-- Ending the tenancy at once breaches the notice duty; ending it after the window is lawful. -/
theorem sample_scenario_breach :
    ¬ Authorized sample.law [⟨1, ⟨"landlord"⟩, ⟨"giveNotice"⟩⟩, ⟨2, ⟨"landlord"⟩, ⟨"endTenancy"⟩⟩] := by
  decide +kernel

theorem sample_scenario_lawful :
    Authorized sample.law [⟨1, ⟨"landlord"⟩, ⟨"giveNotice"⟩⟩, ⟨12, ⟨"landlord"⟩, ⟨"endTenancy"⟩⟩] := by
  decide +kernel

end Charter.Dsl.Sample
