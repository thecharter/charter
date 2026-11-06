import Charter.Eval.Interpreter

/-!
# Charter.Core.Transition — Declarative Transition Relation & Three-Answer Judgment (`G1.4`)

Defines the inductive declarative transition relations (`DeclClock`, `DeclPhraseStep`,
`DeclTraceStep`) and the normative three-answer `EventJudgment` (`occurred`, `lawful`,
`valid`, `Mission Law 2`) against which `Charter.Eval.Properties` proves `evalPhrase_sound`,
`evalPhrase_complete`, `replay_deterministic`, and `clock_never_decreases`.
-/

namespace Charter

/-- The three independent institutional answers on a performed transition (`Mission Law 2`). -/
structure EventJudgment where
  occurred : Bool
  lawful   : Bool
  valid    : Bool
  deriving Repr, DecidableEq

/-- Extract the three independent institutional answers from a `TransInfo` record. -/
def TransInfo.judgment (info : TransInfo) : EventJudgment :=
  { occurred := true
    lawful   := !info.disabled
    valid    := info.valid }

/-- `Mission Law 2` (`T01`–`T03`): lawfulness and institutional validity are orthogonal —
all four `(lawful, valid)` quadrants on an occurred action are distinct and representable. -/
theorem three_answers_independent (te actor : Tagged) :
    ∃ (iLL iLV iUL iUV : TransInfo),
      iLL.judgment = ⟨true, true, true⟩ ∧
      iLV.judgment = ⟨true, true, false⟩ ∧
      iUL.judgment = ⟨true, false, true⟩ ∧
      iUV.judgment = ⟨true, false, false⟩ :=
  ⟨ .mk te [] false false true (some actor) [] .yes .yes [],
    .mk te [] false false false (some actor) [] .yes .no [],
    .mk te [] true true true (some actor) [] .no .yes [],
    .mk te [] true true false (some actor) [] .no .no [],
    rfl, rfl, rfl, rfl ⟩

/-- `T04` (extralegal advisory annotation irrelevance, `docs/rfc.md` §14): any trailing
advisory `Note "..."` on a trigger phrase is erased at `CIR` elaboration and produces the
exact same `Config` and `Output`s. -/
theorem resolvePhrase_trigger_note (spec : Spec) (xs : List Var) (t : Term) (n₁ n₂ : Option String) :
    resolvePhrase spec (.trigger xs t n₁) = resolvePhrase spec (.trigger xs t n₂) := by
  unfold resolvePhrase
  have h10000 : (10000 : Nat) = 9999 + 1 := rfl
  rw [h10000]
  rfl

theorem advisory_note_irrelevant (cfg : Config) (xs : List Var) (t : Term) (n₁ n₂ : Option String) :
    runPhrase cfg (.trigger xs t n₁) = runPhrase cfg (.trigger xs t n₂) := by
  unfold runPhrase
  have hd₁ : Phrase.hasDecls (.trigger xs t n₁) = false := rfl
  have hd₂ : Phrase.hasDecls (.trigger xs t n₂) = false := rfl
  rw [hd₁, hd₂, resolvePhrase_trigger_note cfg.spec xs t n₁ n₂]

/-- Declarative specification of environment clock evaluation on a compiled phrase (`009.1`). -/
inductive DeclClock (spec : Spec) (specIdx : Spec.SpecIndex) (s : State) :
    CPhrase → Except RuntimeError (Option Int) → Prop where
  | tick :
      DeclClock spec specIdx s .tick (.ok (some (s.time + 1)))
  | setTimeOk (t : Term) (t' : Int) :
      (M.eval M.fuel t).run (Ctx.ofIdx spec specIdx s) [] = .ok [.int t'] →
      s.time ≤ t' →
      DeclClock spec specIdx s (.setTime t) (.ok (some t'))
  | setTimeBackwards (t : Term) (t' : Int) :
      (M.eval M.fuel t).run (Ctx.ofIdx spec specIdx s) [] = .ok [.int t'] →
      t' < s.time →
      DeclClock spec specIdx s (.setTime t) (.error (.timeBackwards s.time t'))
  | setTimeEvalErr (t : Term) (e : RuntimeError) :
      (M.eval M.fuel t).run (Ctx.ofIdx spec specIdx s) [] = .error e →
      DeclClock spec specIdx s (.setTime t) (.error e)
  | setTimeBadShape (t : Term) (vs : List Value) :
      (M.eval M.fuel t).run (Ctx.ofIdx spec specIdx s) [] = .ok vs →
      (∀ t' : Int, vs ≠ [.int t']) →
      DeclClock spec specIdx s (.setTime t) (.error (.fuelExhausted "reading the clock"))
  | nonClock (cp : CPhrase) :
      cp ≠ .tick →
      (∀ t : Term, cp ≠ .setTime t) →
      DeclClock spec specIdx s cp (.ok none)

/-- Inductive declarative specification of one complete Charter phrase step (`Law 9`, `G1.4`).
`(cfg : Config)` and `(p : Phrase)` are parameters; every static or runtime failure leaves
`cfg` unchanged (`011.9`). -/
inductive DeclPhraseStep (cfg : Config) (p : Phrase) : Config → List Output → Prop where
  | resolveError (ds : List Diagnostic) :
      resolvePhrase cfg.spec p = .error ds →
      DeclPhraseStep cfg p cfg (ds.map .diag)
  | stratifyError (spec' : Spec) (cp : CPhrase) (ws : List Diagnostic) (cycle : List DomId) :
      resolvePhrase cfg.spec p = .ok (spec', cp, ws) →
      p.hasDecls = true →
      Stratify.strata spec' = .error cycle →
      DeclPhraseStep cfg p cfg
        (ws.map .diag ++ [.diag (Diagnostic.error "CHR020"
          s!"derivation is not stratifiable: {", ".intercalate cycle} depend on their own absence (through Not, Forall, or an aggregate)")])
  | clockError (spec' : Spec) (cp : CPhrase) (ws : List Diagnostic)
      (strata : List (List DomId)) (e : RuntimeError) :
      resolvePhrase cfg.spec p = .ok (spec', cp, ws) →
      (if p.hasDecls then Stratify.strata spec' else .ok cfg.strata) = .ok strata →
      DeclClock spec' spec'.buildIndex cfg.state cp (.error e) →
      DeclPhraseStep cfg p cfg (ws.map .diag ++ [Interp.diagOf e])
  | semError (spec' : Spec) (cp : CPhrase) (ws : List Diagnostic)
      (strata : List (List DomId)) (newTime : Option Int)
      (state0 : State) (outs : List Output) :
      resolvePhrase cfg.spec p = .ok (spec', cp, ws) →
      (if p.hasDecls then Stratify.strata spec' else .ok cfg.strata) = .ok strata →
      DeclClock spec' spec'.buildIndex cfg.state cp (.ok newTime) →
      state0 = (match newTime with
        | some t => { cfg.state with time := t, step := cfg.state.step + 1 }
        | none => { cfg.state with step := cfg.state.step + 1 }) →
      Interp.semPhrase spec' spec'.buildIndex state0 1000 cp = (none, outs) →
      DeclPhraseStep cfg p cfg
        (ws.map .diag ++ (match newTime with | some t => Output.timeSet t :: outs | none => outs))
  | pureReadError (spec' : Spec) (cp : CPhrase) (ws : List Diagnostic)
      (strata : List (List DomId)) (state0 : State) (outs : List Output) (e : RuntimeError) :
      resolvePhrase cfg.spec p = .ok (spec', cp, ws) →
      (if p.hasDecls then Stratify.strata spec' else .ok cfg.strata) = .ok strata →
      DeclClock spec' spec'.buildIndex cfg.state cp (.ok none) →
      p.hasDecls = false →
      state0 = { cfg.state with step := cfg.state.step + 1 } →
      Interp.semPhrase spec' spec'.buildIndex state0 1000 cp = (some [], outs) →
      Interp.checkInvariants spec' spec'.buildIndex state0 = .error e →
      DeclPhraseStep cfg p cfg (ws.map .diag ++ outs ++ [Interp.diagOf e])
  | pureReadOk (spec' : Spec) (cp : CPhrase) (ws : List Diagnostic)
      (strata : List (List DomId)) (state0 : State) (outs : List Output) (invViol : List DomId) :
      resolvePhrase cfg.spec p = .ok (spec', cp, ws) →
      (if p.hasDecls then Stratify.strata spec' else .ok cfg.strata) = .ok strata →
      DeclClock spec' spec'.buildIndex cfg.state cp (.ok none) →
      p.hasDecls = false →
      state0 = { cfg.state with step := cfg.state.step + 1 } →
      Interp.semPhrase spec' spec'.buildIndex state0 1000 cp = (some [], outs) →
      Interp.checkInvariants spec' spec'.buildIndex state0 = .ok invViol →
      DeclPhraseStep cfg p { cfg with spec := spec', state := state0 }
        (ws.map .diag ++ outs ++ invViol.map (fun d => Output.violation (.invariant d)))
  | mutatingError (spec' : Spec) (cp : CPhrase) (ws : List Diagnostic)
      (strata : List (List DomId)) (newTime : Option Int) (state0 : State)
      (store : Store) (outs outs2 : List Output) :
      resolvePhrase cfg.spec p = .ok (spec', cp, ws) →
      (if p.hasDecls then Stratify.strata spec' else .ok cfg.strata) = .ok strata →
      DeclClock spec' spec'.buildIndex cfg.state cp (.ok newTime) →
      (p.hasDecls = true ∨ newTime.isSome = true ∨ store ≠ []) →
      state0 = (match newTime with
        | some t => { cfg.state with time := t, step := cfg.state.step + 1 }
        | none => { cfg.state with step := cfg.state.step + 1 }) →
      Interp.semPhrase spec' spec'.buildIndex state0 1000 cp = (some store, outs) →
      Interp.newContext cfg spec' spec'.buildIndex strata (State.makeAssignments spec' store state0) = (none, outs2) →
      DeclPhraseStep cfg p cfg
        (ws.map .diag ++ (match newTime with | some t => Output.timeSet t :: outs | none => outs) ++ outs2)
  | mutatingOk (cfg' : Config) (spec' : Spec) (cp : CPhrase) (ws : List Diagnostic)
      (strata : List (List DomId)) (newTime : Option Int) (state0 : State)
      (store : Store) (outs outs2 : List Output) :
      resolvePhrase cfg.spec p = .ok (spec', cp, ws) →
      (if p.hasDecls then Stratify.strata spec' else .ok cfg.strata) = .ok strata →
      DeclClock spec' spec'.buildIndex cfg.state cp (.ok newTime) →
      (p.hasDecls = true ∨ newTime.isSome = true ∨ store ≠ []) →
      state0 = (match newTime with
        | some t => { cfg.state with time := t, step := cfg.state.step + 1 }
        | none => { cfg.state with step := cfg.state.step + 1 }) →
      Interp.semPhrase spec' spec'.buildIndex state0 1000 cp = (some store, outs) →
      Interp.newContext cfg spec' spec'.buildIndex strata (State.makeAssignments spec' store state0) = (some cfg', outs2) →
      DeclPhraseStep cfg p cfg'
        (ws.map .diag ++ (match newTime with | some t => Output.timeSet t :: outs | none => outs) ++ outs2)

/-- Multi-step declarative trace relation. -/
inductive DeclTraceStep : Config → List Phrase → Config → List (List Output) → Prop where
  | nil (cfg : Config) : DeclTraceStep cfg [] cfg []
  | cons {cfg cfg₁ cfg₂ : Config} {p : Phrase} {ps : List Phrase} {o : List Output} {os : List (List Output)} :
      DeclPhraseStep cfg p cfg₁ o →
      DeclTraceStep cfg₁ ps cfg₂ os →
      DeclTraceStep cfg (p :: ps) cfg₂ (o :: os)

end Charter
