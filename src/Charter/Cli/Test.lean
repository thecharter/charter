import Charter.Cli.Run

/-!
# Charter.Cli.Test — `charter test <files or directories>`

Runs every `.eflint` file under the given paths in test mode: a file passes when
it produces no error diagnostic and every query holds (`test/eflint-corpus/README.md`).
Prints one line per file and a summary; exit status is non-zero when any file
fails.

**Fixture directives** (plan §5.4, With's style) are comment lines `//! …`
anywhere in the file:

- `//! expect-error: CHR020` — the file passes only if that error is reported
  (several directives, several codes; other outcomes are not checked);
- `//! expect-warning: CHR019` — likewise for a warning;
- `//! known-issue: <why>` — the file is expected to fail; it fails the run if it
  unexpectedly passes (so a fixed issue is noticed and the directive deleted);
- `//! expect-failed-claims: N` — the file passes only if exactly `N` claims fail
  (queries, expectations, or provenance checks) and no error is reported;
- `//! explore: N` — explore enabled acts to depth `N` from the file's end state and
  each scenario's (plan §2.2.7); a violated invariant is a failed claim. `--explore N`
  on the command line sets the depth for every file without the directive;
- `//! explore-domain: <type> = v, a..b, "s"` — the candidates for a component of an act
  whose domain is not enumerable (D15, spec 013.2); without one such an act is reported
  unexplored and that report is a failed claim. `--explore-domain "<type> = …"` adds to it.

With `--expect <file>`, each file's outcome is compared with the outcome recorded
there (lines `ok   <path>` / `FAIL <path>`, the format this command prints, which
`tools/corpus-baseline` produces by running eFLINT itself). With
`--tolerate <file>`, the paths quoted in backticks in that file (the
`tolerances.md` of the corpus) are expected to *differ* from the recorded
outcome, under a ruled decision; a tolerated file that agrees with eFLINT fails
the run, because its tolerance is no longer needed and must be deleted (D2).
`--out json` prints one object per file and a summary object.
-/

namespace Charter.Cli

open Lean (Json)

def walkEflint (p : System.FilePath) : Nat → IO (List System.FilePath)
  | 0 => return []
  | depth + 1 => do
    if ← p.isDir then
      let base := p.fileName.getD ""
      if base == ".git" || base == ".lake" || base == ".charter" || base == ".reference" then
        return []
      let entries ← p.readDir
      let sorted := entries.qsort (fun a b => a.path.toString < b.path.toString)
      let mut acc := []
      for e in sorted do acc := acc ++ (← walkEflint e.path depth)
      return acc
    else if p.extension == some "eflint" || p.extension == some "charter" then return [p]
    else return []

structure TestOpts where
  paths        : List String := []
  expect       : Option String := none
  tolerate     : Option String := none
  metamorphic  : Bool := false
  mutateClaims : Bool := false

def parseTestArgs : List String → TestOpts → Except String TestOpts
  | [], o => .ok { o with paths := o.paths.reverse }
  | "--metamorphic" :: rest, o => parseTestArgs rest { o with metamorphic := true }
  | "--mutate-claims" :: rest, o => parseTestArgs rest { o with mutateClaims := true }
  | "--expect" :: f :: rest, o => parseTestArgs rest { o with expect := some f }
  | ["--expect"], _ => .error "--expect needs a file"
  | "--tolerate" :: f :: rest, o => parseTestArgs rest { o with tolerate := some f }
  | ["--tolerate"], _ => .error "--tolerate needs a file"
  | p :: rest, o => parseTestArgs rest { o with paths := p :: o.paths }

/-- `ok   path` / `FAIL path` lines → (path, passed). Anything after the path is ignored. -/
def readExpected (file : System.FilePath) : IO (List (String × Bool)) := do
  let txt ← IO.FS.readFile file
  return txt.splitOn "\n" |>.filterMap fun line =>
    let ws := line.trim.splitOn " " |>.filter (· != "")
    match ws with
    | "ok" :: p :: _ => some (p, true)
    | "FAIL" :: p :: _ => some (p.takeWhile (· != ':'), false)
    | _ => none

/-- Every backticked token ending in `.eflint` in a Markdown tolerance file. -/
def readToleratedMd (file : System.FilePath) : IO (List String) := do
  let txt ← IO.FS.readFile file
  let parts := txt.splitOn "`"
  let rec pick : List String → Bool → List String
    | [], _ => []
    | s :: rest, inside => (if inside && s.endsWith ".eflint" then [s] else []) ++ pick rest (!inside)
  return pick parts false

/-- Parse a machine-readable `tolerances.json` manifest (validating required schema keys)
and verify parity with sibling `tolerances.md` when present, or read `tolerances.md` directly. -/
def readTolerated (file : System.FilePath) : IO (List String) := do
  if file.extension == some "json" then
    let txt ← IO.FS.readFile file
    let j ← IO.ofExcept (Json.parse txt)
    let arr ← IO.ofExcept (j.getObjValAs? (Array Json) "tolerances")
    let mut paths : List String := []
    for entry in arr do
      let fix ← IO.ofExcept (entry.getObjValAs? String "fixture")
      let _ ← IO.ofExcept (entry.getObjValAs? String "decision")
      let _ ← IO.ofExcept (entry.getObjValAs? String "eflintOutcome")
      let _ ← IO.ofExcept (entry.getObjValAs? String "charterOutcome")
      let _ ← IO.ofExcept (entry.getObjValAs? String "reason")
      paths := paths ++ [fix]
    let mdSibling := file.withExtension "md"
    if ← mdSibling.pathExists then
      let mdPaths := (← readToleratedMd mdSibling).filter (·.startsWith "test/")
      if paths.any (fun p => !mdPaths.contains p) || mdPaths.any (fun p => !paths.contains p) then
        throw (IO.userError s!"tolerance drift between {file} ({paths.length} entries) and {mdSibling} ({mdPaths.length} entries)")
    return paths
  else
    readToleratedMd file

def endsWithPath (full : String) (suffix : String) : Bool :=
  full == suffix || full.endsWith ("/" ++ suffix) || suffix.endsWith ("/" ++ full)

/-- The `//!` directives of a source text. -/
structure Directives where
  expectErrors   : List String := []
  expectWarnings : List String := []
  knownIssue     : Option String := none
  expectFailedClaims : Option Nat := none
  /-- `//! explore: N`: explore enabled acts to depth N from the end states. -/
  explore        : Option Nat := none
  /-- `//! explore-domain: t = v, a..b, "s"`: the candidates for a judged act's component (D15). -/
  exploreMenu    : Explore.Menu := []
  /-- A malformed `explore-domain` line, reported as CHR001 against the file. -/
  menuErrors     : List String := []
  /-- Inline opt-in static assurance gates (`//! require-provenance`, etc.). -/
  assurance      : AssuranceOpts := {}
  /-- `//! metamorphic`: verify invariance under advisory stripping & actor renaming (`T04`, `T05`). -/
  metamorphic    : Bool := false

def readDirectives (src : String) : Directives :=
  src.splitOn "\n" |>.foldl (fun d line =>
    let l := line.trim
    if l.startsWith "//!" then
      let body := (l.drop 3).trim
      if body.startsWith "expect-error:" then { d with expectErrors := d.expectErrors ++ [(body.drop 13).trim] }
      else if body.startsWith "expect-warning:" then { d with expectWarnings := d.expectWarnings ++ [(body.drop 15).trim] }
      else if body.startsWith "known-issue:" then { d with knownIssue := some (body.drop 12).trim }
      else if body.startsWith "expect-failed-claims:" then { d with expectFailedClaims := (body.drop 21).trim.toNat? }
      else if body.startsWith "explore:" then { d with explore := (body.drop 8).trim.toNat? }
      else if body == "metamorphic" then { d with metamorphic := true }
      else if body == "require-provenance" then { d with assurance := { d.assurance with requireProvenance := true } }
      else if body == "forbid-midstream-decls" then { d with assurance := { d.assurance with forbidMidstreamDecls := true } }
      else if body == "require-complete-explore" then { d with assurance := { d.assurance with requireCompleteExplore := true } }
      else if body == "deny-warnings" then { d with assurance := { d.assurance with denyWarnings := true } }
      else if body.startsWith "explore-domain:" then
        match parseMenuLine (body.drop 15).trim with
        | .ok entry => { d with exploreMenu := d.exploreMenu ++ [entry] }
        | .error e => { d with menuErrors := d.menuErrors ++ [e] }
      else d
    else d) {}

-- Collect string constants mentioned inside operative rule conditions of `spec` (`T05`).
mutual
def termStrConsts : Term → List String
  | .stringLit s => [s]
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a | .project a _ | .tag a _ | .untag a =>
    termStrConsts a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .heldFor a b =>
    termStrConsts a ++ termStrConsts b
  | .mulDivRound x n d _ =>
    termStrConsts x ++ termStrConsts n ++ termStrConsts d
  | .fnApp _ k => termStrConsts k
  | .dimLit _ _ => []
  | .ite c t e => termStrConsts c ++ termStrConsts t ++ termStrConsts e
  | .doneAt t | .stampOf t | .overdueOf t => termStrConsts t
  | .calOp1 _ t => termStrConsts t
  | .calOp2 _ t a => termStrConsts t ++ termStrConsts a
  | .exists_ _ t | .forall_ _ t | .count _ t | .sum _ t | .max _ t | .min _ t => termStrConsts t
  | .app _ args => argsStrConsts args
  | .boolLit _ | .intLit _ | .ref _ | .currentTime => []

def argsStrConsts : Args → List String
  | .pos ts => termListStrConsts ts
  | .named ms => termModsStrConsts ms

def termListStrConsts : List Term → List String
  | [] => []
  | t :: ts => termStrConsts t ++ termListStrConsts ts

def termModsStrConsts : List (Var × Term) → List String
  | [] => []
  | (_, t) :: ms => termStrConsts t ++ termModsStrConsts ms
end

def specRuleConstants (spec : Spec) : List String :=
  spec.decls.flatMap fun (_, t) =>
    let dC := t.derivation.flatMap fun
      | .dv _ tm | .holdsWhen tm => termStrConsts tm
      | .defeasibleDAG _ rs => rs.flatMap fun r => termStrConsts r.cond ++ (match r.conseq with | .holdsBool _ => [] | .yieldsVal vt => termStrConsts vt)
    let cC := t.conditions.flatMap termStrConsts
    let fC := termStrConsts t.domainConstraint
    let kC := match t.kind with
      | .act a => a.validWhen.flatMap termStrConsts
      | .duty du => du.violatedWhen.flatMap termStrConsts
      | .immunity im => im.unlessConds.flatMap termStrConsts
      | _ => []
    dC ++ cC ++ fC ++ kC

mutual
def permuteTerm (perm : List (String × String)) : Term → Term
  | .stringLit s => .stringLit ((perm.find? (·.1 == s)).map (·.2) |>.getD s)
  | .not a => .not (permuteTerm perm a)
  | .and a b => .and (permuteTerm perm a) (permuteTerm perm b)
  | .or a b => .or (permuteTerm perm a) (permuteTerm perm b)
  | .leq a b => .leq (permuteTerm perm a) (permuteTerm perm b)
  | .geq a b => .geq (permuteTerm perm a) (permuteTerm perm b)
  | .ge a b => .ge (permuteTerm perm a) (permuteTerm perm b)
  | .le a b => .le (permuteTerm perm a) (permuteTerm perm b)
  | .sub a b => .sub (permuteTerm perm a) (permuteTerm perm b)
  | .add a b => .add (permuteTerm perm a) (permuteTerm perm b)
  | .mult a b => .mult (permuteTerm perm a) (permuteTerm perm b)
  | .mod a b => .mod (permuteTerm perm a) (permuteTerm perm b)
  | .div a b => .div (permuteTerm perm a) (permuteTerm perm b)
  | .eq a b => .eq (permuteTerm perm a) (permuteTerm perm b)
  | .neq a b => .neq (permuteTerm perm a) (permuteTerm perm b)
  | .exists_ xs t => .exists_ xs (permuteTerm perm t)
  | .forall_ xs t => .forall_ xs (permuteTerm perm t)
  | .count xs t => .count xs (permuteTerm perm t)
  | .sum xs t => .sum xs (permuteTerm perm t)
  | .max xs t => .max xs (permuteTerm perm t)
  | .min xs t => .min xs (permuteTerm perm t)
  | .when a b => .when (permuteTerm perm a) (permuteTerm perm b)
  | .present a => .present (permuteTerm perm a)
  | .violated a => .violated (permuteTerm perm a)
  | .enabled a => .enabled (permuteTerm perm a)
  | .evStatus w a => .evStatus w (permuteTerm perm a)
  | .hasConflict a => .hasConflict (permuteTerm perm a)
  | .project a x => .project (permuteTerm perm a) x
  | .tag a d => .tag (permuteTerm perm a) d
  | .untag a => .untag (permuteTerm perm a)
  | .app d args => .app d (permuteArgs perm args)
  | .heldFor a b => .heldFor (permuteTerm perm a) (permuteTerm perm b)
  | .mulDivRound x n d m => .mulDivRound (permuteTerm perm x) (permuteTerm perm n) (permuteTerm perm d) m
  | .fnApp d k => .fnApp d (permuteTerm perm k)
  | .ite c t e => .ite (permuteTerm perm c) (permuteTerm perm t) (permuteTerm perm e)
  | .doneAt t => .doneAt (permuteTerm perm t)
  | .stampOf t => .stampOf (permuteTerm perm t)
  | .calOp1 op t => .calOp1 op (permuteTerm perm t)
  | .calOp2 op t a => .calOp2 op (permuteTerm perm t) (permuteTerm perm a)
  | .overdueOf t => .overdueOf (permuteTerm perm t)
  | t => t

def permuteArgs (perm : List (String × String)) : Args → Args
  | .pos ts => .pos (permuteTermList perm ts)
  | .named ms => .named (permuteTermMods perm ms)

def permuteTermList (perm : List (String × String)) : List Term → List Term
  | [] => []
  | t :: ts => permuteTerm perm t :: permuteTermList perm ts

def permuteTermMods (perm : List (String × String)) : List (Var × Term) → List (Var × Term)
  | [] => []
  | (x, t) :: ms => (x, permuteTerm perm t) :: permuteTermMods perm ms
end

mutual
def stripAdvisoryDecl : Decl → Option Decl
  | .atPos p d => (stripAdvisoryDecl d).map (.atPos p)
  | .clause _ => none
  | .document .. => none
  | .typeExt d cls k =>
    let cls' := cls.filter fun mc => match mc.stripPos with | .fromSpan _ _ => false | _ => true
    some (.typeExt d cls' k)
  | .module n ps body =>
    some (.module n ps (stripAdvisoryDecls body))
  | d => some d
termination_by structural x => x

def stripAdvisoryDecls : List Decl → List Decl
  | [] => []
  | d :: rest =>
    match stripAdvisoryDecl d with
    | some d' => d' :: stripAdvisoryDecls rest
    | none => stripAdvisoryDecls rest
termination_by structural x => x
end

mutual
def stripAdvisoryPhrase : Phrase → Phrase
  | .trigger xs t _ => .trigger xs t none
  | .decls ds => .decls (stripAdvisoryDecls ds)
  | .par ps => .par (stripAdvisoryList ps)
  | .scenario name ps _ => .scenario name (stripAdvisoryList ps) []
  | p => p

def stripAdvisoryList : List Phrase → List Phrase
  | [] => []
  | p :: ps => stripAdvisoryPhrase p :: stripAdvisoryList ps
end

mutual
def permutePhrase (perm : List (String × String)) : Phrase → Phrase
  | .trigger xs t _ => .trigger xs (permuteTerm perm t) none
  | .create xs t => .create xs (permuteTerm perm t)
  | .terminate xs t => .terminate xs (permuteTerm perm t)
  | .obfuscate xs t => .obfuscate xs (permuteTerm perm t)
  | .query t => .query (permuteTerm perm t)
  | .instQuery b xs t => .instQuery b xs (permuteTerm perm t)
  | .par ps => .par (permutePhraseList perm ps)
  | .scenario name ps spans => .scenario name (permutePhraseList perm ps) spans
  | .expect w neg t => .expect w neg (permuteTerm perm t)
  | .setTime t => .setTime (permuteTerm perm t)
  | .why t => .why (permuteTerm perm t)
  | .submitEvidence pol t src => .submitEvidence pol (permuteTerm perm t) src
  | .retractEvidence t src => .retractEvidence (permuteTerm perm t) src
  | p => p

def permutePhraseList (perm : List (String × String)) : List Phrase → List Phrase
  | [] => []
  | p :: ps => permutePhrase perm p :: permutePhraseList perm ps
end

/-- Execute `phrases` (including `Scenario`s) purely and return `(errors, failedClaims, judgmentSignature)`. -/
def evalMetamorphicSignature (phrases : List Phrase) : Nat × Nat × List (TriBool × TriBool × Bool) := Id.run do
  let mut cfg : Config := {}
  let mut errs := 0
  let mut fails := 0
  let mut sig : List (TriBool × TriBool × Bool) := []
  let procOuts (outs : List Output) : Nat × Nat × List (TriBool × TriBool × Bool) := Id.run do
    let mut e := 0
    let mut fl := 0
    let mut sg : List (TriBool × TriBool × Bool) := []
    for o in outs do
      match o with
      | .diag dg => if dg.isError then e := e + 1
      | .queryRes ok => if !ok then fl := fl + 1
      | .expectRes _ _ ok => if !ok then fl := fl + 1
      | .executed info => sg := sg ++ [(info.lawfulTri, info.validTri, info.valid)]
      | _ => pure ()
    return (e, fl, sg)
  for p in phrases do
    match p with
    | .scenario _ ps _ =>
      let mut scCfg := cfg
      for sp in ps do
        let (c', outs) := runPhrase scCfg sp
        scCfg := c'
        let (e, fl, sg) := procOuts outs
        errs := errs + e; fails := fails + fl; sig := sig ++ sg
    | _ =>
      let (c', outs) := runPhrase cfg p
      cfg := c'
      let (e, fl, sg) := procOuts outs
      errs := errs + e; fails := fails + fl; sig := sig ++ sg
  return (errs, fails, sig)

/-- Run `T04` (advisory stripping) and `T05` (non-salient actor permutation) metamorphic checks. -/
def checkMetamorphicImpartiality (path : System.FilePath) : IO (Option String) := do
  let (items, loadDiags) ← loadProgram path
  if loadDiags.any Diagnostic.isError then return none
  let phrases := items.filterMap fun l => match l.item.val with | .inr p => some p | .inl _ => none
  let baseSig := evalMetamorphicSignature phrases
  -- 1. T04: strip all Clause, Document, From, and Note advisory metadata
  let strippedSig := evalMetamorphicSignature (stripAdvisoryList phrases)
  if strippedSig != baseSig then
    return some "metamorphic T04 failure: stripping advisory Note/Clause/From metadata changed verdicts"
  -- 2. T05: build cyclic permutation over interchangeable enumeration atoms
  let mut finalSpec := emptySpec
  for p in phrases do
    match resolvePhrase finalSpec p with
    | .ok (s', _, _) => finalSpec := s'
    | .error _ => pure ()
  let salient := specRuleConstants finalSpec
  let mut perm : List (String × String) := []
  for (_, ts) in finalSpec.decls do
    match ts.domain with
    | .strings ss =>
      let freeAtoms := ss.filter fun a => !salient.contains a
      if freeAtoms.length ≥ 2 then
        let rotated := freeAtoms.drop 1 ++ [freeAtoms.headD ""]
        perm := perm ++ (freeAtoms.zip rotated)
    | _ => pure ()
  if !perm.isEmpty then
    let permSig := evalMetamorphicSignature (permutePhraseList perm phrases)
    if permSig != baseSig then
      return some "metamorphic T05 failure: permuting interchangeable actor/entity atoms changed verdicts"
  return none

/-- Flip a claim phrase (`?t` <-> `?!t`, `?w t` <-> `?!w t`) for `#69` claim-mutation testing. -/
def flipClaimPhrase : Phrase → Option (Phrase × String)
  | .query (.not inner) => some (.query inner, s!"?!{inner}")
  | .query t => some (.query (.not t), s!"?{t}")
  | .expect w neg t => some (.expect w (!neg) t, s!"?{if neg then "" else "!"}{w.name} {t}")
  | _ => none

/-- Flip each claim in `path` one at a time (`#69` `--mutate-claims`) and report any mutant that still passes. -/
def checkClaimMutations (path : System.FilePath) (scenFilter : List String) : IO (Nat × List String) := do
  let (items, loadDiags) ← loadProgram path
  if loadDiags.any Diagnostic.isError then return (0, [])
  let claimOutsPass (outs : List Output) : Bool :=
    outs.all fun
      | .queryRes ok => ok
      | .expectRes _ _ ok => ok
      | .diag d => !d.isError
      | _ => true
  let mut cfg : Config := {}
  let mut specIdx : Spec.SpecIndex := cfg.spec.buildIndex
  let mut totalMutants := 0
  let mut survivors : List String := []
  for l in items do
    match l.item.val with
    | .inl _ => pure ()
    | .inr (.scenario name ps spans) =>
      cfg := { cfg with spec := cfg.spec.insertScenario name spans }
      if scenFilter.isEmpty || scenFilter.contains name then
        let mut scCfg := cfg
        let mut scIdx := specIdx
        let mut idx := 0
        for p in ps do
          let pPos := match l.item.subPos[idx]? with
            | some qp => if qp.line == 0 then l.item.pos else qp
            | none => l.item.pos
          idx := idx + 1
          if let some (flipped, label) := flipClaimPhrase p then
            totalMutants := totalMutants + 1
            let (_, _, flipOuts) := runPhraseCached scCfg scIdx true flipped
            if claimOutsPass flipOuts then
              survivors := survivors ++ [
                s!"{l.file}:{pPos.line}:{pPos.col} [scenario {name}]: survived claim mutation `{label}` (flipping claim still passed — vacuous or unexercised)"
              ]
          let (scCfg', scIdx', _) := runPhraseCached scCfg scIdx true p
          scCfg := scCfg'
          scIdx := scIdx'
    | .inr p =>
      if scenFilter.isEmpty then
        if let some (flipped, label) := flipClaimPhrase p then
          totalMutants := totalMutants + 1
          let (_, _, flipOuts) := runPhraseCached cfg specIdx true flipped
          if claimOutsPass flipOuts then
            survivors := survivors ++ [
              s!"{l.file}:{l.item.pos.line}:{l.item.pos.col}: survived claim mutation `{label}` (flipping claim still passed — vacuous or unexercised)"
            ]
      let (cfg', nextIdx, _) := runPhraseCached cfg specIdx true p
      cfg := cfg'
      specIdx := nextIdx
  return (totalMutants, survivors)

/-- The verdict on a file: passed, and why in one phrase. -/
def verdict (d : Directives) (denyWarnings : Bool) (stats : RunStats) : Bool × String :=
  if !d.expectErrors.isEmpty || !d.expectWarnings.isEmpty then
    let missing := (d.expectErrors ++ d.expectWarnings).filter (fun c => !stats.codes.contains c)
    if missing.isEmpty then (true, s!"expected diagnostics reported: {", ".intercalate (d.expectErrors ++ d.expectWarnings)}")
    else (false, s!"expected diagnostics missing: {", ".intercalate missing}; reported: {", ".intercalate stats.codes}")
  else match d.expectFailedClaims, d.knownIssue with
    | some n, _ =>
      let totalFailed := stats.failedQueries + stats.failedProvenance
      if stats.errors == 0 && totalFailed == n && (!denyWarnings || stats.warnings == 0) then
        (true, s!"exactly {n} failed claim(s), as expected")
      else (false, s!"expected exactly {n} failed claim(s) and no error; got {totalFailed} and {stats.errors} error(s)")
    | none, some why =>
      if stats.ok denyWarnings then (false, s!"known issue unexpectedly passes ({why}); delete the directive")
      else (true, s!"known issue, still failing ({why})")
    | none, none =>
      let provNote := if stats.failedProvenance > 0 then s!", {stats.failedProvenance} failed provenance check(s)" else ""
      let warnNote := if denyWarnings && stats.warnings > 0 then s!", {stats.warnings} denied warning(s)" else ""
      (stats.ok denyWarnings, s!"{stats.errors} error(s), {stats.failedQueries} failed claim(s){provNote}{warnNote}")

/-- `charter test <paths…> [--expect file] [--tolerate file] [--out json]` -/
def testCommand (args : List String) : IO UInt32 := do
  let fl ← match takeFlags args with
    | .error e => IO.eprintln s!"charter test: {e}"; return 2
    | .ok r => pure r
  let json := fl.json
  let opts ← match parseTestArgs fl.rest {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter test: {e}"; return 2
  if opts.paths.isEmpty then
    IO.eprintln "usage: charter test <file.eflint | directory> ... [--scenario <name>] [--expect <outcomes>] [--tolerate <tolerances.md>] [--out json] [--eflint]"
    return 2
  let expected ← match opts.expect with
    | some f => readExpected f
    | none => pure []
  let tolerated ← match opts.tolerate with
    | some f => readTolerated f
    | none => pure []
  let mut files : List System.FilePath := []
  for a in opts.paths do files := files ++ (← walkEflint a 32)
  let mut passed := 0
  let mut agreed := 0
  let mut toleratedCount := 0
  let mut failed : List String := []
  let report (f : System.FilePath) (ok : Bool) (why : String) (extra : List (String × Json)) : IO Unit :=
    if json then IO.println (Json.mkObj (([("kind", Json.str "file"), ("file", Json.str f.toString), ("ok", Json.bool ok), ("why", Json.str why)] : List (String × Json)) ++ extra)).compress
    else IO.println s!"{if ok then "ok  " else "FAIL"} {f}{if ok then " (" ++ why ++ ")" else ": " ++ why}"
  for f in files do
    let src ← IO.FS.readFile f
    let d := readDirectives src
    let depth := d.explore.getD fl.explore
    for e in d.menuErrors do
      IO.eprintln s!"{f}: error CHR001: {e}"
    let menu := d.exploreMenu ++ fl.exploreMenu
    let assurance : AssuranceOpts := {
      requireProvenance := d.assurance.requireProvenance || fl.assurance.requireProvenance
      forbidMidstreamDecls := d.assurance.forbidMidstreamDecls || fl.assurance.forbidMidstreamDecls
      requireCompleteExplore := d.assurance.requireCompleteExplore || fl.assurance.requireCompleteExplore
      denyWarnings := d.assurance.denyWarnings || fl.assurance.denyWarnings
    }
    let stats ← runProgram { testMode := true, json, eflint := fl.eflint, scenarios := true, scenarioFilter := fl.scenarios, explore := depth, exploreMenu := menu, assurance } f
    let stats := if d.menuErrors.isEmpty then stats else { stats with errors := stats.errors + d.menuErrors.length }
    let metaErr? ← if opts.metamorphic || d.metamorphic then checkMetamorphicImpartiality f else pure none
    if let some me := metaErr? then IO.eprintln s!"{f}: error: {me}"
    let stats := if metaErr?.isSome then { stats with errors := stats.errors + 1 } else stats
    let (mutTotal, mutSurv) ← if opts.mutateClaims && stats.ok assurance.denyWarnings then
        checkClaimMutations f fl.scenarios
      else pure (0, [])
    for surv in mutSurv do
      IO.eprintln surv
    let stats := if mutSurv.isEmpty then stats else { stats with failedQueries := stats.failedQueries + mutSurv.length }
    let (outcome, why0) := verdict d assurance.denyWarnings stats
    let why := if opts.mutateClaims && outcome then s!"{why0}, {mutTotal}/{mutTotal} mutated claim(s) killed"
               else if opts.mutateClaims && !mutSurv.isEmpty then s!"{mutSurv.length}/{mutTotal} mutated claim(s) survived"
               else why0
    let fS := f.toString
    let isTolerated := tolerated.any (endsWithPath fS)
    match expected.find? (fun (p, _) => endsWithPath fS p) with
    | some (_, eflintOk) =>
      let agrees := outcome == eflintOk
      let ok := if isTolerated then !agrees else agrees
      let eflintS := if eflintOk then "passes" else "fails"
      let charterS := if outcome then "passes" else "fails"
      let extra := [("eflint", Json.str eflintS), ("charter", Json.str charterS), ("tolerated", Json.bool isTolerated)]
      if ok then
        passed := passed + 1
        if isTolerated then
          toleratedCount := toleratedCount + 1
          report f true s!"tolerated: eFLINT {eflintS}, Charter {charterS}" extra
        else
          agreed := agreed + 1
          report f true s!"{charterS} as in eFLINT; {stats.phrases} phrases" extra
      else
        failed := failed ++ [fS]
        if isTolerated then report f false s!"listed as tolerated but agrees with eFLINT ({charterS}); delete the tolerance" extra
        else report f false s!"eFLINT {eflintS}, Charter {charterS} ({why})" extra
    | none =>
      if opts.expect.isSome && !json then
        IO.println s!"WARN {f}: no eFLINT outcome recorded; judged on its own"
      if outcome then passed := passed + 1 else failed := failed ++ [fS]
      report f outcome why []
  let detail := if opts.expect.isSome then s!" ({agreed} agree with eFLINT, {toleratedCount} tolerated differences)" else ""
  if json then
    IO.println (Json.mkObj [("kind", "summary"), ("passed", Json.num passed), ("failed", Json.num failed.length),
      ("total", Json.num files.length), ("agree", Json.num agreed), ("tolerated", Json.num toleratedCount)]).compress
  else
    IO.println s!"{passed} passed, {failed.length} failed, {files.length} total{detail}"
  return (if failed.isEmpty then 0 else 1)

end Charter.Cli
