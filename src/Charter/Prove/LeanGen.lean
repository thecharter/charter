import Charter.Prove.Slice

/-!
# Charter.Prove.LeanGen — Slice-Framed Incremental Proof Project Generator (`013.4`, `#74`)

Emits a checkpointed chain of constructive kernel theorems (`Charter.Prove.Slice`):
1. **Per-step slice certificates (`StepSlice`)**: resolves, evaluates, and saturates only the
   read/write cone of each phrase (`stepSummarySliced`);
2. **Pointer-equal frame sharing (`reframeSpec` / `reframeState`)**: emits only the per-step
   delta of `Spec` and `State` over `sl.declaredDoms` / `sl.coneDoms`, so the checker elaborates
   and reduces `O(|slice|)` terms rather than re-elaborating all 700+ declared types;
3. **Chunked list literals (`emitChunkedList`)**: splits any fallback list literal longer than
   20 items into typed sub-lists so list elaboration stays strictly linear.
-/

namespace Charter.Prove

structure Obligation where
  name     : String
  about    : String
  text     : String
  line     : Nat
  expected : Bool
  deriving Repr, Inhabited

structure Step where
  name  : String
  about : String
  line  : Nat
  deriving Repr, Inhabited

abbrev Loc := String × Nat

structure Project where
  files       : List (String × String)
  decided     : String × Loc
  steps       : List (Step × Loc)
  obligations : List (Obligation × Loc)

def ident (s : String) : String :=
  let body := s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  let body := String.mk body
  if body.isEmpty || (body.get 0).isDigit then "n_" ++ body else body

def reprSource [Repr α] (x : α) : String := (reprPrec x 0).pretty 100000000

def phraseSource (p : Phrase) : String := reprSource p

def boolsSource (bs : List Bool) : String := "[" ++ ", ".intercalate (bs.map fun b => if b then "true" else "false") ++ "]"
def stringsSource (ss : List String) : String := "[" ++ ", ".intercalate (ss.map String.quote) ++ "]"

def summarySource (cfgName : String) (s : Summary) : String :=
  s!"\{ cfg := {cfgName}, verdicts := {boolsSource s.verdicts}, violated := {stringsSource s.violated} }"

def aboutOf (text : String) : String :=
  if text.startsWith "?lawful" || text.startsWith "?!lawful" then "lawful"
  else if text.startsWith "?valid" || text.startsWith "?!valid" then "valid"
  else if text.startsWith "?violated" || text.startsWith "?!violated" then "violated"
  else "holds"

/-- Emit a `List α` in typed chunks of at most `chunkSz` elements so Lean's list literal
elaborator never nests `List.cons` deeper than `chunkSz` (`#74`). -/
def emitChunkedList [Repr α] (elemType pfx : String) (chunkSz : Nat) (xs : List α) :
    List String × String :=
  if xs.isEmpty then ([], "[]")
  else if xs.length <= chunkSz then ([], reprSource xs)
  else
    let rec splitChunks : Nat → List α → List (List α)
      | 0, rem => if rem.isEmpty then [] else [rem]
      | _ + 1, [] => []
      | k + 1, rem => rem.take chunkSz :: splitChunks k (rem.drop chunkSz)
    let chunks := splitChunks (xs.length + 1) xs
    let defs := chunks.zipIdx.map fun (ch, idx) =>
      s!"def {pfx}_{idx} : List ({elemType}) := {reprSource ch}"
    let expr := " ++ ".intercalate ((List.range chunks.length).map fun idx => s!"{pfx}_{idx}")
    (defs, expr)

def emitFullSpecDefs (specName : String) (sp : Spec) : List String :=
  let (dDefs, dExpr) := emitChunkedList "Charter.DomId × Charter.TypeSpec" (specName ++ "_dc") 20 sp.decls
  let (cDefs, cExpr) := emitChunkedList "Charter.Clause" (specName ++ "_cc") 15 sp.clauses
  dDefs ++ cDefs ++ [
    s!"def {specName} : Charter.Spec := \{ decls := {dExpr}, aliases := {reprSource sp.aliases}, clauses := {cExpr}, document := {reprSource sp.document}, documents := {reprSource sp.documents}, modules := {reprSource sp.modules}, temporalProperties := {reprSource sp.temporalProperties}, scenarios := {reprSource sp.scenarios}, regimes := {reprSource sp.regimes}, amendBodies := {reprSource sp.amendBodies}, amendMigrations := {reprSource sp.amendMigrations}, amendProcedure := {reprSource sp.amendProcedure}, tracksHistory := {reprSource sp.tracksHistory}, rankEdges := {reprSource sp.rankEdges}, serviceInterfaceDeclared := {reprSource sp.serviceInterfaceDeclared}, exposedActs := {reprSource sp.exposedActs}, exposedInputs := {reprSource sp.exposedInputs}, actorKeys := {reprSource sp.actorKeys} }"
  ]

def emitFullStateDefs (stName : String) (st : State) : List String :=
  let (cDefs, cExpr) := emitChunkedList "Charter.Tagged × Charter.Info" (stName ++ "_sc") 25 st.contents
  cDefs ++ [
    s!"def {stName} : Charter.State := \{ contents := {cExpr}, time := {reprSource st.time}, step := {st.step} }"
  ]

structure Gen where
  lines      : Array String := #[]
  module     : String
  files      : Array (String × String) := #[]
  comment    : String
  inChunk    : Nat := 0
  chunk      : Nat
  stem       : String
  cur        : Summary := S0
  curName    : String := "Charter.Prove.S0"
  cfgName    : String := "Charter.Prove.S0.cfg"
  specName   : String := "Charter.Prove.S0.cfg.spec"
  strataName : String := "Charter.Prove.S0.cfg.strata"
  specDepth  : Nat := 0
  updDepth   : Nat := 0
  stateDepth : Nat := 0
  chain      : Array String := #[]
  items      : Array String := #[]
  steps      : Array (Step × Loc) := #[]

def Gen.nextLoc (g : Gen) : Loc := (g.module, g.lines.size + 1)

def Gen.push (g : Gen) (ls : List String) : Gen := { g with lines := g.lines ++ ls.toArray }

def importLines (prev : Option String) : List String :=
  ["import Charter.Prove.Slice", "import Charter.Prove.Kernel"] ++ (prev.map (fun m => [s!"import {m}"])).getD []
    ++ ["set_option maxRecDepth 100000", ""]

def Gen.newModule (g : Gen) : Gen :=
  let next := s!"{ident g.stem}_steps_{g.files.size + 2}"
  { g with files := g.files.push (g.module, "\n".intercalate g.lines.toList ++ "\n"),
           module := next, inChunk := 0,
           lines := (g.comment :: importLines (some g.module)).toArray }

def Gen.chunked (g : Gen) (forceSmall : Bool := false) : Gen :=
  let lim := if forceSmall then min g.chunk 4 else g.chunk
  if g.inChunk ≥ lim && lim > 0 then g.newModule else g

def sameContentsAndTime (a b : State) : Bool :=
  a.time == b.time && reprStr a.contents == reprStr b.contents

/-- Checkpoint one phrase over its verified `StepSlice` (`#74`). -/
def Gen.checkpoint (g : Gen) (tag : String) (p : Phrase) (line : Nat) (about : String) :
    Gen × String × String × String := Id.run do
  let pName := s!"p_{tag}"
  let slName := s!"sl_{tag}"
  let cfgName := s!"cfg_{tag}"
  let sName := s!"S_{tag}"
  let thm := s!"step_{tag}"
  let (sl0, next) := computeVerifiedStepSlice g.cur p
  -- Sub-batch large saturation cones (`> 5` batches, e.g. Genesis & successor onboarding) to 4 layers per batch
  -- so even multi-quantifier top-stratum invariants stay under ~2 GB RSS (`#74`)!
  let sl := if !sl0.useFull && sl0.strataBatches.length > 5 then
      { sl0 with strataBatches := groupStrataBatches 4 (sl0.strataBatches.flatten) }
    else sl0
  let totalLayers := sl.strataBatches.foldl (fun acc b => acc + b.length) 0
  let multiBatch := !sl.useFull && (sl.strataBatches.length > 1 || (p.hasDecls && totalLayers >= 4))
  -- Isolate saturation-heavy or huge-AST steps into their own fresh module
  let heavySat := sl.useFull || totalLayers >= 4 || (reprStr p).length > 6000
  let g := if heavySat && g.inChunk > 0 then g.newModule else g

  let specChanged := p.hasDecls || next.cfg.lawVersion != g.cur.cfg.lawVersion
  let batchDefs : List String :=
    if multiBatch then
      sl.strataBatches.zipIdx.map fun (b, bi) =>
        s!"def batch_{tag}_{bi} : List (List Charter.DomId) := {reprSource b}"
    else []
  let slExpr : String :=
    if multiBatch then
      let bRefs := "[" ++ ", ".intercalate ((List.range sl.strataBatches.length).map fun bi => s!"batch_{tag}_{bi}") ++ "]"
      s!"\{ useFull := {reprSource sl.useFull}, isDeclSlice := {reprSource sl.isDeclSlice}, resolveDoms := {reprSource sl.resolveDoms}, readWriteDoms := {reprSource sl.readWriteDoms}, declaredDoms := {reprSource sl.declaredDoms}, updatedDoms := {reprSource sl.updatedDoms}, coneDoms := {reprSource sl.coneDoms}, strataBatches := {bRefs}, nextStrata := {reprSource sl.nextStrata} }"
    else reprSource sl
  let mut preDefs : List String := [
    s!"-- line {line}",
    s!"def {pName} : Charter.Phrase := {phraseSource p}" ] ++
    batchDefs ++ [
    s!"def {slName} : Charter.Prove.StepSlice := {slExpr}"
  ]

  let mut flatSpecThm? : Option String := none
  let mut flatStateThm? : Option String := none
  let mut nextSpecDepth := g.specDepth
  let mut nextUpdDepth := g.updDepth
  let mut nextStateDepth := g.stateDepth
  let mut nextSpecName := g.specName
  let mut nextStrataName := g.strataName
  if specChanged then
    nextSpecName := s!"spec_{tag}"
    nextStrataName := s!"strata_{tag}"
    if !sl.useFull && sl.isDeclSlice then
      let deltaSpec : Spec := {
        next.cfg.spec with
        decls := next.cfg.spec.decls.filter (fun (d, _) => sl.declaredDoms.contains d)
        clauses := next.cfg.spec.clauses.filter (fun c => !g.cur.cfg.spec.clauses.any (fun oc => reprStr oc == reprStr c))
      }
      let dSpecName := s!"dspec_{tag}"
      let hitUpd := if sl.updatedDoms.isEmpty then g.updDepth else g.updDepth + 1
      if g.specDepth >= 22 || hitUpd >= 3 then
        preDefs := preDefs ++ emitFullSpecDefs dSpecName deltaSpec ++
          emitFullSpecDefs nextSpecName next.cfg.spec ++ [
          s!"def {nextSpecName}_reframed : Charter.Spec := Charter.Prove.reframeSpec {slName}.declaredDoms {slName}.updatedDoms {g.specName} {dSpecName}",
          s!"theorem flat_sp_{tag} : {nextSpecName}_reframed = {nextSpecName} := by kernel_rfl",
          s!"def {nextStrataName} : List (List Charter.DomId) := {slName}.nextStrata"
        ]
        flatSpecThm? := some s!"flat_sp_{tag}"
        nextSpecDepth := 0
        nextUpdDepth := 0
      else
        preDefs := preDefs ++ emitFullSpecDefs dSpecName deltaSpec ++ [
          s!"def {nextSpecName} : Charter.Spec := Charter.Prove.reframeSpec {slName}.declaredDoms {slName}.updatedDoms {g.specName} {dSpecName}",
          s!"def {nextStrataName} : List (List Charter.DomId) := {slName}.nextStrata"
        ]
        nextSpecDepth := g.specDepth + 1
        nextUpdDepth := hitUpd
    else
      let (strDefs, strExpr) := emitChunkedList "List Charter.DomId" (nextStrataName ++ "_c") 25 next.cfg.strata
      preDefs := preDefs ++ emitFullSpecDefs nextSpecName next.cfg.spec ++ strDefs ++ [
        s!"def {nextStrataName} : List (List Charter.DomId) := {strExpr}"
      ]
      nextSpecDepth := 0
      nextUpdDepth := 0

  -- Emit `State` via `reframeState` delta when sliced, or 1-line `step` bump when read-only!
  let mut stateExprForSummary := ""
  if !specChanged && sameContentsAndTime g.cur.cfg.state next.cfg.state &&
     g.cur.cfg.violatedDuties == next.cfg.violatedDuties then
    stateExprForSummary := s!"\{ {g.cfgName}.state with step := {next.cfg.state.step} }"
    preDefs := preDefs ++ [
      s!"def {cfgName} : Charter.Config := \{ {g.cfgName} with state := {stateExprForSummary} }"
    ]
  else if !sl.useFull && (!sl.isDeclSlice || (!sl.strataBatches.isEmpty || next.cfg.state.contents.length != g.cur.cfg.state.contents.length)) then
    if sameContentsAndTime g.cur.cfg.state next.cfg.state then
      stateExprForSummary := s!"\{ {g.cfgName}.state with step := {next.cfg.state.step} }"
      preDefs := preDefs ++ [
        s!"def {cfgName} : Charter.Config := \{ spec := {nextSpecName}, strata := {nextStrataName}, state := {stateExprForSummary}, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} }"
      ]
    else
      let coneEntries := next.cfg.state.contents.filter (fun q => sl.coneDoms.contains q.1.2)
      let dStName := s!"dst_{tag}"
      let stName := s!"st_{tag}"
      if g.stateDepth >= 12 then
        preDefs := preDefs ++
          emitFullStateDefs dStName { contents := coneEntries, time := next.cfg.state.time, step := next.cfg.state.step } ++
          emitFullStateDefs stName next.cfg.state ++ [
          s!"def {stName}_reframed : Charter.State := Charter.Prove.reframeState {slName}.coneDoms {g.cfgName}.state {dStName}",
          s!"theorem flat_st_{tag} : {stName}_reframed = {stName} := by kernel_rfl",
          s!"def {cfgName} : Charter.Config := \{ spec := {nextSpecName}, strata := {nextStrataName}, state := {stName}, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} }"
        ]
        stateExprForSummary := stName
        flatStateThm? := some s!"flat_st_{tag}"
        nextStateDepth := 0
      else
        preDefs := preDefs ++ emitFullStateDefs dStName { contents := coneEntries, time := next.cfg.state.time, step := next.cfg.state.step } ++ [
          s!"def {stName} : Charter.State := Charter.Prove.reframeState {slName}.coneDoms {g.cfgName}.state {dStName}",
          s!"def {cfgName} : Charter.Config := \{ spec := {nextSpecName}, strata := {nextStrataName}, state := {stName}, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} }"
        ]
        stateExprForSummary := stName
        nextStateDepth := g.stateDepth + 1
  else
    let stName := s!"st_{tag}"
    preDefs := preDefs ++ emitFullStateDefs stName next.cfg.state ++ [
      s!"def {cfgName} : Charter.Config := \{ spec := {nextSpecName}, strata := {nextStrataName}, state := {stName}, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} }"
    ]
    stateExprForSummary := stName
    nextStateDepth := 0

  let g := g.push preDefs
  let g := if flatSpecThm?.isSome || flatStateThm?.isSome then g.newModule else g
  let rawSpecExpr := if flatSpecThm?.isSome then s!"{nextSpecName}_reframed" else nextSpecName
  let rawStExpr := if flatStateThm?.isSome then s!"st_{tag}_reframed" else stateExprForSummary
  let fRws : List String :=
    (match flatSpecThm? with | some th => [th] | none => []) ++
    (match flatStateThm? with | some th => [th] | none => [])

  -- Multi-batch saturation decomposition (`sl.strataBatches.length > 1`, `#74`):
  -- Each 18-stratum batch runs in its own isolated checker module and composes with zero axioms!
  if multiBatch then
    if let .sat setup := stepSlicedPre g.cur sl p then
      let mut gm := g
      let wspName := s!"wsp_{tag}"
      let prevName := s!"prev_{tag}"
      let sb0Name := s!"sbatch_{tag}_0"
      let setupName := s!"setup_{tag}"
      let preStart := gm.nextLoc
      let (prevDefs, prevExpr) := emitChunkedList "Charter.Tagged × Charter.Info" (prevName ++ "_c") 25 setup.prevFacts
      let setupNextSpec := if sl.isDeclSlice then rawSpecExpr else g.specName
      let setupNextStrata := if sl.isDeclSlice then nextStrataName else g.strataName
      let useFlatWsp := setup.workSpec.decls.length > 80
      let wspFlatName := s!"wsp_flat_{tag}"
      let wspDefs : List String :=
        if useFlatWsp then
          [s!"def {wspName} : Charter.Spec := Charter.Prove.projectSpec {slName}.readWriteDoms {setupNextSpec}"]
        else
          emitFullSpecDefs wspName setup.workSpec
      gm := gm.push (
        wspDefs ++
        prevDefs ++ [s!"def {prevName} : List (Charter.Tagged × Charter.Info) := {prevExpr}"] ++
        emitFullStateDefs sb0Name setup.s0 ++ [
        s!"def {setupName} : Charter.Prove.SatSetup := \{ workSpec := {wspName}, nextSpec := {setupNextSpec}, nextStrata := {setupNextStrata}, prevFacts := {prevName}, s0 := {sb0Name}, verdictDelta := {boolsSource setup.verdictDelta} }",
        s!"theorem hpre_{tag} : Charter.Prove.stepSlicedPre {g.curName} {slName} {pName} = Charter.Prove.StepPreOutcome.sat {setupName} := by kernel_rfl",
        "" ])
      gm := { gm with steps := gm.steps.push ({ name := s!"hpre_{tag}", about, line }, preStart) }

      if useFlatWsp then
        gm := gm.newModule
        let fwStart := gm.nextLoc
        gm := gm.push (
          emitFullSpecDefs wspFlatName setup.workSpec ++ [
          s!"theorem hwsp_{tag} : {setupName}.workSpec = {wspFlatName} := by kernel_rfl",
          "" ])
        gm := { gm with steps := gm.steps.push ({ name := s!"hwsp_{tag}", about, line }, fwStart) }

      let mut curBatchSt := setup.s0
      for (batch, bi) in sl.strataBatches.zipIdx do
        gm := gm.newModule
        let nextBatchSt := match runStrataBatch setup.workSpec setup.prevFacts curBatchSt batch with
          | .ok st' => st'
          | .error _ => curBatchSt
        let sbPrev := s!"sbatch_{tag}_{bi}"
        let sbNext := s!"sbatch_{tag}_{bi + 1}"
        let bStart := gm.nextLoc
        -- Share `sbPrev.contents` suffix by pointer whenever `runStrataBatch` purely prepended new derived entries!
        let addedCount := nextBatchSt.contents.length - curBatchSt.contents.length
        let sbNextDefs : List String :=
          if nextBatchSt.contents.length >= curBatchSt.contents.length &&
             reprStr (nextBatchSt.contents.drop addedCount) == reprStr curBatchSt.contents &&
             bi % 8 != 7 then
            if addedCount == 0 then
              [s!"def {sbNext} : Charter.State := {sbPrev}"]
            else
              let (adDefs, adExpr) := emitChunkedList "Charter.Tagged × Charter.Info" (sbNext ++ "_ad") 25 (nextBatchSt.contents.take addedCount)
              adDefs ++ [s!"def {sbNext} : Charter.State := \{ {sbPrev} with contents := {adExpr} ++ {sbPrev}.contents }"]
          else
            emitFullStateDefs sbNext nextBatchSt
        if useFlatWsp then
          gm := gm.push (
            sbNextDefs ++ [
            s!"theorem hsat_raw_{tag}_{bi} : Charter.Prove.runStrataBatch {wspFlatName} {setupName}.prevFacts {sbPrev} batch_{tag}_{bi} = Except.ok {sbNext} := by kernel_rfl",
            s!"theorem hsat_{tag}_{bi} : Charter.Prove.runStrataBatch {setupName}.workSpec {setupName}.prevFacts {sbPrev} batch_{tag}_{bi} = Except.ok {sbNext} := Eq.trans (congrArg (fun (sp : Charter.Spec) => Charter.Prove.runStrataBatch sp {setupName}.prevFacts {sbPrev} batch_{tag}_{bi}) hwsp_{tag}) hsat_raw_{tag}_{bi}",
            "" ])
        else
          gm := gm.push (
            sbNextDefs ++ [
            s!"theorem hsat_{tag}_{bi} : Charter.Prove.runStrataBatch {setupName}.workSpec {setupName}.prevFacts {sbPrev} batch_{tag}_{bi} = Except.ok {sbNext} := by kernel_rfl",
            "" ])
        gm := { gm with steps := gm.steps.push ({ name := s!"hsat_{tag}_{bi}", about, line }, bStart) }
        curBatchSt := nextBatchSt

      gm := gm.newModule
      let m := sl.strataBatches.length
      let finalBatchStName := s!"sbatch_{tag}_{m}"
      let stepFnExpr := s!"(Charter.Prove.runStrataBatch {setupName}.workSpec {setupName}.prevFacts)"
      let chainTerm := (List.range m).foldr
        (fun bi acc => s!"(Charter.Prove.foldlM_cons_ok {stepFnExpr} hsat_{tag}_{bi} {acc})")
        s!"(Charter.Prove.foldlM_nil_ok {stepFnExpr} {finalBatchStName})"
      let postStart := gm.nextLoc
      let postSetupExpr := if useFlatWsp then s!"\{ {setupName} with workSpec := {wspFlatName} }" else setupName
      let mkPostBridge (targetS : String) : List String :=
        if useFlatWsp then [
          s!"theorem hpost_raw_{tag} : Charter.Prove.stepSlicedPost {g.curName} {slName} {postSetupExpr} {finalBatchStName} = {targetS} := by kernel_rfl",
          s!"theorem hpost_{tag} : Charter.Prove.stepSlicedPost {g.curName} {slName} {setupName} {finalBatchStName} = {targetS} := Eq.trans (congrArg (fun (sp : Charter.Spec) => Charter.Prove.stepSlicedPost {g.curName} {slName} \{ {setupName} with workSpec := sp } {finalBatchStName}) hwsp_{tag}) hpost_raw_{tag}"
        ] else [
          s!"theorem hpost_{tag} : Charter.Prove.stepSlicedPost {g.curName} {slName} {setupName} {finalBatchStName} = {targetS} := by kernel_rfl"
        ]
      if fRws.isEmpty then
        gm := gm.push ([
          s!"def {sName} : Charter.Prove.Summary := {summarySource cfgName next}" ] ++
          mkPostBridge sName ++ [
          s!"theorem {thm} : Charter.Prove.stepSummarySliced {g.curName} {slName} {pName} = {sName} := Charter.Prove.stepSummarySliced_of_batches hpre_{tag} {chainTerm} hpost_{tag}",
          "" ])
      else
        let rawCfgName := s!"{cfgName}_reframed"
        let rawSName := s!"{sName}_reframed"
        let flatProof : String := match flatSpecThm?, flatStateThm? with
          | some spTh, none =>
            s!"congrArg (fun (sp : Charter.Spec) => (\{ cfg := (\{ spec := sp, strata := {nextStrataName}, state := {stateExprForSummary}, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} } : Charter.Config), verdicts := {boolsSource next.verdicts}, violated := {stringsSource next.violated} } : Charter.Prove.Summary)) {spTh}"
          | none, some stTh =>
            s!"congrArg (fun (st : Charter.State) => (\{ cfg := (\{ spec := {nextSpecName}, strata := {nextStrataName}, state := st, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} } : Charter.Config), verdicts := {boolsSource next.verdicts}, violated := {stringsSource next.violated} } : Charter.Prove.Summary)) {stTh}"
          | some spTh, some stTh =>
            s!"Eq.trans (congrArg (fun (sp : Charter.Spec) => (\{ cfg := (\{ spec := sp, strata := {nextStrataName}, state := st_{tag}_reframed, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} } : Charter.Config), verdicts := {boolsSource next.verdicts}, violated := {stringsSource next.violated} } : Charter.Prove.Summary)) {spTh}) (congrArg (fun (st : Charter.State) => (\{ cfg := (\{ spec := {nextSpecName}, strata := {nextStrataName}, state := st, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} } : Charter.Config), verdicts := {boolsSource next.verdicts}, violated := {stringsSource next.violated} } : Charter.Prove.Summary)) {stTh})"
          | none, none => "rfl"
        gm := gm.push ([
          s!"def {rawCfgName} : Charter.Config := \{ spec := {rawSpecExpr}, strata := {nextStrataName}, state := {rawStExpr}, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} }",
          s!"def {rawSName} : Charter.Prove.Summary := {summarySource rawCfgName next}" ] ++
          mkPostBridge rawSName ++ [
          s!"theorem {thm}_raw : Charter.Prove.stepSummarySliced {g.curName} {slName} {pName} = {rawSName} := Charter.Prove.stepSummarySliced_of_batches hpre_{tag} {chainTerm} hpost_{tag}",
          s!"def {sName} : Charter.Prove.Summary := {summarySource cfgName next}",
          s!"theorem {thm}_flat : {rawSName} = {sName} := {flatProof}",
          s!"theorem {thm} : Charter.Prove.stepSummarySliced {g.curName} {slName} {pName} = {sName} := Eq.trans {thm}_raw {thm}_flat",
          "" ])
      gm := { gm with cur := next, curName := sName, cfgName := cfgName,
                      specName := nextSpecName, strataName := nextStrataName,
                      specDepth := nextSpecDepth, updDepth := nextUpdDepth, stateDepth := nextStateDepth,
                      inChunk := 1,
                      steps := gm.steps.push ({ name := thm, about, line }, postStart) }
      gm := gm.newModule
      return (gm, slName, pName, sName)

  let start := g.nextLoc
  if fRws.isEmpty then
    let g := g.push [
      s!"def {sName} : Charter.Prove.Summary := {summarySource cfgName next}",
      s!"theorem {thm} : Charter.Prove.stepSummarySliced {g.curName} {slName} {pName} = {sName} := by kernel_rfl",
      "" ]
    let g := { g with cur := next, curName := sName, cfgName := cfgName,
                      specName := nextSpecName, strataName := nextStrataName,
                      specDepth := nextSpecDepth, updDepth := nextUpdDepth, stateDepth := nextStateDepth,
                      inChunk := g.inChunk + 1,
                      steps := g.steps.push ({ name := thm, about, line }, start) }
    let g := if heavySat then g.newModule else g
    return (g, slName, pName, sName)
  else
    -- Never run `show`/`rw` on `stepSummarySliced` in the elaborator (`013.4` Meta.whnf blowup):
    -- close `step_<tag>_raw` by `kernel_rfl` against the reframed record, then `Eq.trans` onto flat `S_<tag>`!
    let rawCfgName := s!"{cfgName}_reframed"
    let rawSName := s!"{sName}_reframed"
    let flatProof : String := match flatSpecThm?, flatStateThm? with
      | some spTh, none =>
        s!"congrArg (fun (sp : Charter.Spec) => (\{ cfg := (\{ spec := sp, strata := {nextStrataName}, state := {stateExprForSummary}, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} } : Charter.Config), verdicts := {boolsSource next.verdicts}, violated := {stringsSource next.violated} } : Charter.Prove.Summary)) {spTh}"
      | none, some stTh =>
        s!"congrArg (fun (st : Charter.State) => (\{ cfg := (\{ spec := {nextSpecName}, strata := {nextStrataName}, state := st, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} } : Charter.Config), verdicts := {boolsSource next.verdicts}, violated := {stringsSource next.violated} } : Charter.Prove.Summary)) {stTh}"
      | some spTh, some stTh =>
        s!"Eq.trans (congrArg (fun (sp : Charter.Spec) => (\{ cfg := (\{ spec := sp, strata := {nextStrataName}, state := st_{tag}_reframed, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} } : Charter.Config), verdicts := {boolsSource next.verdicts}, violated := {stringsSource next.violated} } : Charter.Prove.Summary)) {spTh}) (congrArg (fun (st : Charter.State) => (\{ cfg := (\{ spec := {nextSpecName}, strata := {nextStrataName}, state := st, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} } : Charter.Config), verdicts := {boolsSource next.verdicts}, violated := {stringsSource next.violated} } : Charter.Prove.Summary)) {stTh})"
      | none, none => "rfl"
    let g := g.push [
      s!"def {rawCfgName} : Charter.Config := \{ spec := {rawSpecExpr}, strata := {nextStrataName}, state := {rawStExpr}, violatedDuties := {reprSource next.cfg.violatedDuties}, lawVersion := {next.cfg.lawVersion} }",
      s!"def {rawSName} : Charter.Prove.Summary := {summarySource rawCfgName next}",
      s!"theorem {thm}_raw : Charter.Prove.stepSummarySliced {g.curName} {slName} {pName} = {rawSName} := by kernel_rfl",
      s!"def {sName} : Charter.Prove.Summary := {summarySource cfgName next}",
      s!"theorem {thm}_flat : {rawSName} = {sName} := {flatProof}",
      s!"theorem {thm} : Charter.Prove.stepSummarySliced {g.curName} {slName} {pName} = {sName} := Eq.trans {thm}_raw {thm}_flat",
      "" ]
    let g := { g with cur := next, curName := sName, cfgName := cfgName,
                      specName := nextSpecName, strataName := nextStrataName,
                      specDepth := nextSpecDepth, updDepth := nextUpdDepth, stateDepth := nextStateDepth,
                      inChunk := g.inChunk + 1,
                      steps := g.steps.push ({ name := thm, about, line }, start) }
    let g := if heavySat then g.newModule else g
    return (g, slName, pName, sName)

def Gen.item (g : Gen) (k : Nat) (it : Item) : Gen :=
  match it.val with
  | .inl _ => g
  | .inr p =>
    let isHeavy := p.hasDecls || (match p with | .par ps => ps.length > 5 | _ => false)
    let g := g.chunked isHeavy
    match p.scenarioParts with
    | none =>
      let (g, slName, pName, _) := g.checkpoint (toString k) p it.pos.line "phrase"
      { g with chain := g.chain.push s!"Charter.Prove.foldl_phrase_sliced step_{k}",
               items := g.items.push s!"Charter.Prove.SlicedItem.phrase {slName} {pName}" }
    | some (name, ps, _) => Id.run do
      let forkName := g.curName
      let forkCfg := g.cfgName
      let forkSpec := g.specName
      let forkStrata := g.strataName
      let forkCur := g.cur
      let mut g := g
      let mut pairExprs : Array String := #[]
      let mut stepNames : Array String := #[]
      let mut j := 0
      for q in ps do
        let qLine := match it.subPos[j]? with
          | some qp => if qp.line == 0 then it.pos.line else qp.line
          | none => it.pos.line
        j := j + 1
        if g.inChunk ≥ min g.chunk 4 && g.chunk > 0 then
          g := g.newModule
        let (g', slName, pName, _) := g.checkpoint s!"{k}_{j}" q qLine "phrase"
        g := g'
        pairExprs := pairExprs.push s!"({slName}, {pName})"
        stepNames := stepNames.push s!"step_{k}_{j}"
      if g.inChunk > 0 then
        g := g.newModule
      let endName := g.curName
      let scen := s!"scen_{k}"
      let scenProof := if stepNames.isEmpty then "rfl"
        else "by rw [" ++ ", ".intercalate (stepNames.toList.map fun s => s!"Charter.Prove.foldl_step_sliced {s}") ++ ", List.foldl_nil]"
      let (isl, viol) := computeVerifiedInvSlice g.cur
      let islName := s!"isl_{k}"
      let vName := s!"S_{k}_v"
      let after := afterScenario forkCur viol
      let sName := s!"S_{k}"
      let start := g.nextLoc
      g := g.push [
        s!"theorem {scen} : [{", ".intercalate pairExprs.toList}].foldl Charter.Prove.stepSlicedPair {forkName} = {endName} := {scenProof}",
        s!"def {islName} : Charter.Prove.InvariantSlice := {reprSource isl}",
        s!"def {vName} : Charter.Prove.Summary := {summarySource g.cfgName viol}",
        s!"theorem viol_{k} : Charter.Prove.addViolatedSliced {islName} {endName} = {vName} := by kernel_rfl",
        s!"def {sName} : Charter.Prove.Summary := {summarySource forkCfg after}",
        s!"theorem after_{k} : Charter.Prove.afterScenario {forkName} {vName} = {sName} := rfl",
        "" ]
      g := { g with cur := after, curName := sName, cfgName := forkCfg,
                    specName := forkSpec, strataName := forkStrata,
                    steps := g.steps.push ({ name := s!"viol_{k}", about := "scenario", line := it.pos.line }, start),
                    chain := g.chain.push s!"Charter.Prove.foldl_scenario_sliced {scen} viol_{k} after_{k}",
                    items := g.items.push s!"Charter.Prove.SlicedItem.scenario {String.quote name} [{", ".intercalate pairExprs.toList}] {islName}" }
      return g

def generate (program stem : String) (rawItems : List Item) (chunk : Nat := 10) : Project := Id.run do
  let baseItems := rawItems.filter fun it => match it.val with | .inr _ => true | .inl _ => false
  let items := splitLargeItems S0 baseItems
  let comment := s!"-- Written by `charter prove` for {program}. Do not edit: it is regenerated on every run."
  let header := comment :: importLines none ++ [
    "/-! Checkpointed slice-framed proof chain (013.4, #74): each step executes over its",
    "verified read/write slice (`Charter.Prove.Slice`) and is decided in the proof kernel. -/",
    "" ]
  let mut g : Gen := { lines := header.toArray, module := s!"{ident stem}_steps_1", comment, chunk, stem }
  let mut k := 0
  for it in items do
    k := k + 1
    g := g.item k it
  if g.inChunk > 0 then
    g := g.newModule
  let (finIsl, fin) := computeVerifiedInvSlice g.cur
  let finStart := g.nextLoc
  g := g.push [
    "-- the program's end state (013.2)",
    s!"def isl_fin : Charter.Prove.InvariantSlice := {reprSource finIsl}",
    s!"def S_fin : Charter.Prove.Summary := {summarySource g.cfgName fin}",
    s!"theorem viol_final : Charter.Prove.addViolatedSliced isl_fin {g.curName} = S_fin := by kernel_rfl",
    "" ]
  g := { g with steps := g.steps.push ({ name := "viol_final", about := "program", line := 0 }, finStart) }
  g := { g with files := g.files.push (g.module, "\n".intercalate g.lines.toList ++ "\n"),
                module := stem, lines := (comment :: importLines (some g.module)).toArray }

  let mut chunkChainBlock : List String := []
  let mut runDecidedBody : List String := []
  if g.items.size <= 25 then
    let itemLines := match g.items.toList.reverse with
      | [] => ["  ]"]
      | last :: rest => (rest.reverse.map (· ++ ",")).map ("  " ++ ·) ++ ["  " ++ last, "  ]"]
    chunkChainBlock := ["/-- The program's slice-annotated items. -/", "def items : List Charter.Prove.SlicedItem := ["] ++ itemLines ++ [""]
    runDecidedBody :=
      ["  unfold Charter.Prove.summarizeSliced items"] ++
      (g.chain.toList.map fun c => s!"  rw [{c}]") ++
      ["  rw [List.foldl_nil, viol_final]"]
  else
    let rec mkPairs : Nat → List (String × String) → List (List (String × String))
      | 0, rem => if rem.isEmpty then [] else [rem]
      | _ + 1, [] => []
      | c + 1, rem => rem.take 20 :: mkPairs c (rem.drop 20)
    -- Track starting and ending `Summary` constant names per item for O(20) chunk sub-lemmas!
    let paired := g.items.toList.zip g.chain.toList
    let pChunks := mkPairs (paired.length + 1) paired
    let icDefs := pChunks.zipIdx.map fun (ch, idx) =>
      s!"def items_c_{idx} : List Charter.Prove.SlicedItem := [{", ".intercalate (ch.map (·.1))}]"
    let joined := " ++ ".intercalate ((List.range pChunks.length).map fun idx => s!"items_c_{idx}")
    let foldlAppHelper := [
      "private theorem foldl_app_sliced (f : Charter.Prove.Summary → Charter.Prove.SlicedItem → Charter.Prove.Summary) :",
      "    ∀ (xs ys : List Charter.Prove.SlicedItem) (s : Charter.Prove.Summary),",
      "      (xs ++ ys).foldl f s = ys.foldl f (xs.foldl f s)",
      "  | [], _, _ => rfl",
      "  | x :: xs, ys, s => by",
      "    rw [List.cons_append, List.foldl_cons, List.foldl_cons]",
      "    exact foldl_app_sliced f xs ys (f s x)",
      ""
    ]
    let subLemmas := pChunks.zipIdx.flatMap fun (ch, idx) =>
      let startS := if idx == 0 then "Charter.Prove.S0" else
        -- last item of previous chunk `idx - 1`: extract `S_<m>` from its chain step!
        let prevLast := (pChunks[idx - 1]!).getLast!
        let cStr := prevLast.2
        if (cStr.splitOn "after_").length > 1 then
          "S_" ++ ((cStr.splitOn "after_").getLast!).trim
        else
          "S_" ++ ((cStr.splitOn "step_").getLast!).trim
      let endS :=
        let curLast := ch.getLast!
        let cStr := curLast.2
        if (cStr.splitOn "after_").length > 1 then
          "S_" ++ ((cStr.splitOn "after_").getLast!).trim
        else
          "S_" ++ ((cStr.splitOn "step_").getLast!).trim
      [ s!"private theorem run_chunk_{idx} : items_c_{idx}.foldl Charter.Prove.stepSlicedItem {startS} = {endS} := by",
        s!"  unfold items_c_{idx}" ] ++
      (ch.map fun (_, c) => s!"  rw [{c}]") ++
      [ "  rfl", "" ]
    chunkChainBlock := ["/-- The program's slice-annotated items. -/"] ++ icDefs ++
      [s!"def items : List Charter.Prove.SlicedItem := {joined}", ""] ++
      foldlAppHelper ++ subLemmas
    let chunkNames := ", ".intercalate ((List.range pChunks.length).map fun idx => s!"run_chunk_{idx}")
    runDecidedBody := [
      "  unfold Charter.Prove.summarizeSliced items",
      "  repeat' rw [foldl_app_sliced]",
      s!"  rw [{chunkNames}, viol_final]"
    ]

  g := g.push chunkChainBlock
  let chainStart := g.nextLoc
  g := g.push ([
    "-- The chain: every checkpoint in order, then the end state.",
    "theorem run_decided : Charter.Prove.summarizeSliced isl_fin items = S_fin := by" ] ++
    runDecidedBody ++ [
    "",
    s!"theorem program_decided : Charter.Prove.summarySliced isl_fin items = ({boolsSource fin.verdicts}, {stringsSource fin.violated}) := by",
    "  unfold Charter.Prove.summarySliced",
    "  show ((Charter.Prove.summarizeSliced isl_fin items).verdicts, (Charter.Prove.summarizeSliced isl_fin items).violated) = _",
    "  rw [run_decided]",
    "  exact rfl",
    "#print axioms program_decided",
    "" ])
  let labels := claimLabels items
  let (vDefs, vExpr) := emitChunkedList "Bool" "fin_verdicts" 30 fin.verdicts
  if !vDefs.isEmpty then
    -- note: `boolsSource` for <=500 booleans is tiny (<3 KB), keep direct `boolsSource` so `rfl` on `[i]?` is immediate!
    pure ()
  let _ := vExpr
  let claimObls : List Obligation := (labels.zip fin.verdicts).zipIdx.map fun (((line, text), ok), i) =>
    { name := s!"claim_{i + 1}", about := aboutOf (text.trim), text, line, expected := ok }
  let invObls : List Obligation := fin.cfg.spec.invariants.map fun d =>
    { name := s!"invariant_{ident d}", about := "invariant", text := d, line := 0, expected := !fin.violated.contains d }
  let mut obls : Array (Obligation × Loc) := #[]
  for (o, i) in claimObls.zipIdx do
    let stmt := s!"theorem {o.name} : (Charter.Prove.summarySliced isl_fin items).1[{i}]? = some true := by rw [program_decided]; rfl"
    obls := obls.push (o, (g.module, g.nextLoc.2 + 1))
    g := g.push [s!"-- line {o.line}: {o.text}", stmt, s!"#print axioms {o.name}", ""]
  for o in invObls do
    let stmt := s!"theorem {o.name} : (Charter.Prove.summarySliced isl_fin items).2.contains {String.quote o.text} = false := by rw [program_decided]; rfl"
    obls := obls.push (o, (g.module, g.nextLoc.2 + 1))
    g := g.push [s!"-- invariant {o.text} holds at the program's end state and at every scenario's (013.2)", stmt, s!"#print axioms {o.name}", ""]
  let files := g.files.push (g.module, "\n".intercalate g.lines.toList ++ "\n")
  return { files := files.toList, decided := ("program_decided", chainStart),
           steps := g.steps.toList, obligations := obls.toList }

end Charter.Prove
