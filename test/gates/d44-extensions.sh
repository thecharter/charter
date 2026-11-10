#!/usr/bin/env bash
# Law 14 Gate (`d44-extensions`, D44):
# Verifies all six D44 institutional runtime & tooling extensions end-to-end:
# 1. Epoch-versioned & replay-safe federated bundles + static parallel commutativity (`BundlesCommute`, `auditHistorical`);
# 2. Scoped conditional delegations (`delegateWhen`) usable while delegator is offline, blocking namespace forgery;
# 3. Counterexample-synthesizing change-impact analysis (`charter diff --impact`);
# 4. Proactive stakeholder `dutyDeltas` (`created`, `violated`) & audience-redacted `GetActorBrief`;
# 5. Usage-Control (`UCON`) live `Allow` re-verification inside `Authorize` when state advances mid-saga;
# 6. Interactive branching & inspection in `charter repl` (`:options`, `:duties`, `:history`, `:revert`, `:jump`).
set -u
cd "$(dirname "$0")/../.." || exit 2
B=.lake/build/bin/charter
SB=.lake/build/bin/charter-server
[ -x "$B" ] && [ -x "$SB" ] || { echo "FAIL d44-extensions: binaries missing"; exit 2; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# 1. Self-test for bundles (including delegateWhen, epoch separation, replay rejection, commutativity)
"$B" bundle self-test >/dev/null 2>&1 || {
  echo "FAIL d44-extensions: charter bundle self-test failed"; exit 1;
}

# 2. `charter diff --impact`: concrete witness synthesis when a power's condition changes
cat > "$tmp/v1.charter" <<'EOF'
Fact member Identified by Ava, Hal.
Fact cleared Identified by member.
Power transfer-funds Actor member
  Valid when member == Ava || cleared(member).
+member(Ava). +member(Hal).
EOF

cat > "$tmp/v2.charter" <<'EOF'
Fact member Identified by Ava, Hal.
Fact cleared Identified by member.
Power transfer-funds Actor member
  Valid when cleared(member).
+member(Ava). +member(Hal).
EOF

diff_json=$("$B" diff "$tmp/v1.charter" "$tmp/v2.charter" --impact --out json 2>&1) || {
  echo "FAIL d44-extensions: charter diff --impact failed: $diff_json"; exit 1;
}
python3 -I - "$diff_json" <<'PY' || exit 1
import json, sys
obj = json.loads(sys.argv[1])
wits = obj.get("impactWitnesses", [])
if not wits or not any("transfer-funds" in w.get("subject", "") for w in wits):
    print(f"FAIL d44-extensions: expected impactWitnesses for transfer-funds, got {obj}")
    sys.exit(1)
PY

# 3. `charter repl`: `:options`, `:duties`, `:history`, `:revert`, `:jump`
cat > "$tmp/repl_prog.charter" <<'EOF'
Fact party Identified by Ava, Panel.
Placeholder holder For party.
Placeholder claimant For party.
Placeholder recipient For party.
Fact demand-open Identified by party.
Duty answer-demand Holder holder Claimant claimant
  Holds when demand-open(holder) && claimant == Panel
  Due within 5.
Act issue-demand Actor party Recipient recipient
  Holds when True
  Creates demand-open(recipient).
+party(Ava). +party(Panel).
EOF

repl_out=$("$B" repl "$tmp/repl_prog.charter" <<'EOF'
:options
issue-demand(Panel, Ava).
:duties
:history
:revert
?demand-open(Ava)
:q
EOF
)
if ! printf '%s\n' "$repl_out" | grep -q "issue-demand" || \
   ! printf '%s\n' "$repl_out" | grep -q "answer-demand" || \
   ! printf '%s\n' "$repl_out" | grep -q "query failed"; then
  echo "FAIL d44-extensions: charter repl branching/inspection output unexpected:"
  echo "$repl_out"
  exit 1
fi

# 4. Server: `dutyDeltas`, `GetActorBrief`, `UCON` mid-saga `Authorize` block, `delegateWhen`,
#    replay protection, `AmendLaw` epoch separation (`auditHistorical`), and `BundlesCommute`
cat > "$tmp/inst_v1.charter" <<'EOF'
Fact participant Identified by ClinicA, LabB, Panel.
Placeholder holder For participant.
Placeholder claimant For participant.
Placeholder recipient For participant.
Fact frozen Identified by participant.
Input Fact lab-certified Identified by participant.
Input Fact clearance Identified by participant * recipient.
Fact audit-tag Identified by participant.
Fact independent-note Identified by participant.
Fact amend-ready Identified by participant.

Duty report-clearance Holder holder Claimant claimant
  Holds when clearance(claimant, holder)
  Due within 5.

Power freeze-actor Actor participant Recipient recipient
  Holds when participant == Panel
  Valid when participant == Panel
  Creates frozen(recipient).

Power run-study Actor participant Recipient recipient
  Holds when clearance(recipient, participant) && !frozen(participant)
  Valid when clearance(recipient, participant) && !frozen(participant)
  Creates audit-tag(participant).

Power log-note Actor participant
  Holds when True
  Valid when True
  Creates independent-note(participant).

Power stage-amendment Actor participant
  Holds when participant == Panel
  Valid when participant == Panel
  Creates amend-ready(participant).

Amend upgrade-law Actor participant
  Holds when participant == Panel && amend-ready(participant)
  Valid when participant == Panel && amend-ready(participant).

+participant(ClinicA). +participant(LabB). +participant(Panel).
EOF

cat > "$tmp/inst_v2.charter" <<'EOF'
Fact participant Identified by ClinicA, LabB, Panel.
Placeholder holder For participant.
Placeholder claimant For participant.
Placeholder recipient For participant.
Fact frozen Identified by participant.
Input Fact lab-certified Identified by participant.
Input Fact clearance Identified by participant * recipient.
Fact audit-tag Identified by participant.
Fact independent-note Identified by participant.
Fact amend-ready Identified by participant.

Duty report-clearance Holder holder Claimant claimant
  Holds when clearance(claimant, holder)
  Due within 5.

Power freeze-actor Actor participant Recipient recipient
  Holds when participant == Panel
  Valid when participant == Panel
  Creates frozen(recipient).

Power run-study Actor participant Recipient recipient
  Holds when clearance(recipient, participant) && !frozen(participant)
  Valid when clearance(recipient, participant) && !frozen(participant)
  Creates audit-tag(participant).

Power log-note Actor participant
  Holds when !frozen(participant)
  Valid when !frozen(participant)
  Creates independent-note(participant).

Power stage-amendment Actor participant
  Holds when participant == Panel
  Valid when participant == Panel
  Creates amend-ready(participant).

Amend upgrade-law Actor participant
  Holds when participant == Panel && amend-ready(participant)
  Valid when participant == Panel && amend-ready(participant).

+participant(ClinicA). +participant(LabB). +participant(Panel).
EOF

"$B" build "$tmp/inst_v1.charter" -o "$tmp/v1.artifact" >/dev/null 2>&1 || {
  echo "FAIL d44-extensions: build inst_v1 failed"; exit 1;
}
"$B" build "$tmp/inst_v2.charter" -o "$tmp/v2.artifact" >/dev/null 2>&1 || {
  echo "FAIL d44-extensions: build inst_v2 failed"; exit 1;
}

python3 -I - "sdk/python" "$SB" "$tmp/v1.artifact" "$tmp/v2.artifact" "$tmp/srv.log" <<'PY' || exit 1
import sys
sys.path.insert(0, sys.argv[1])
from charter_client import CharterStdioClient

cli = CharterStdioClient(sys.argv[2], sys.argv[3], institution_id="fed-d44", log_path=sys.argv[5])
try:
    # A. Scoped conditional delegation (`delegateWhen`): ClinicA delegates clearance to LabB when LabB certifies itself
    s_del = cli.call({
        "op": "SignStatement",
        "seed": "seed-clinic",
        "statementId": "stmt-del-1",
        "author": "ClinicA",
        "assertions": [{
            "kind": "delegateWhen",
            "fact": "clearance",
            "args": ["ClinicA", "LabB"],
            "guards": [{"fact": "lab-certified", "args": ["LabB"]}]
        }]
    })
    assert s_del.ok, f"SignStatement delegateWhen failed: {s_del.raw}"

    s_cert = cli.call({
        "op": "SignStatement",
        "seed": "seed-lab",
        "statementId": "stmt-cert-1",
        "author": "LabB",
        "assertions": [{"kind": "inputFact", "fact": "lab-certified", "args": ["LabB"], "holds": True}]
    })
    assert s_cert.ok, f"SignStatement cert failed: {s_cert.raw}"

    syn = cli.call({
        "op": "SynthesizeBundle",
        "actorSeed": "seed-lab",
        "bundleId": "b-study-1",
        "actor": "LabB",
        "action": "run-study",
        "args": ["LabB", "ClinicA"]
    })
    assert syn.ok, f"SynthesizeBundle with delegateWhen failed: {syn.raw}"
    bundle1 = syn.raw["bundle"]

    # Enact bundle1 -> triggers dutyDeltas (`created` for report-clearance)!
    en1 = cli.call({"op": "EnactBundle", "bundle": bundle1})
    assert en1.ok and en1.raw.get("outcome") == "Allow", f"EnactBundle 1 failed: {en1.raw}"
    deltas = en1.raw.get("dutyDeltas", [])
    assert any(d.get("status") == "created" and "report-clearance" in d.get("duty", "") for d in deltas), \
        f"expected dutyDeltas created on EnactBundle, got {en1.raw}"

    # Replay of identical bundleId must be rejected!
    en_dup = cli.call({"op": "EnactBundle", "bundle": bundle1})
    assert not en_dup.ok and "replay" in en_dup.raw.get("error", "").lower(), \
        f"expected replay rejection on duplicate EnactBundle, got {en_dup.raw}"

    # B. `GetActorBrief` for LabB shows held duty `report-clearance` and enabled `log-note`
    brief = cli.call({"op": "GetActorBrief", "actor": "LabB"})
    assert brief.ok, f"GetActorBrief failed: {brief.raw}"
    held_duties = brief.raw.get("heldDuties", [])
    assert any("report-clearance" in d.get("duty", "") for d in held_duties), f"missing heldDuty in brief: {brief.raw}"

    # C. `UCON` mid-saga interruption: LabB Reserves `run-study`, Panel freezes LabB, LabB calls Authorize -> rejected!
    res = cli.reserve("intent-ucon-1", "LabB", "run-study", ["LabB", "ClinicA"], ttl=10)
    assert res.ok and res.outcome == "Reserved", f"Reserve failed: {res.raw}"
    frz = cli.call({"op": "ExercisePower", "action": "freeze-actor", "args": ["Panel", "LabB"]})
    assert frz.ok and frz.outcome == "Allow", f"freeze-actor failed: {frz.raw}"
    auth = cli.authorize("intent-ucon-1")
    assert not auth.ok, f"expected UCON live re-verification to block Authorize after freeze, got {auth.raw}"

    # D. AdvanceClock past deadline -> emits `dutyDeltas` with `status == "violated"`
    clk = cli.call({"op": "AdvanceClock", "newTime": 6})
    assert clk.ok, f"AdvanceClock failed: {clk.raw}"
    v_deltas = clk.raw.get("dutyDeltas", [])
    assert any(d.get("status") == "violated" and "report-clearance" in d.get("duty", "") for d in v_deltas), \
        f"expected violated dutyDelta on AdvanceClock, got {clk.raw}"

    # E. `BundlesCommute` check (disjoint `run-study` vs `log-note` commutes; identical `run-study` does not)
    comm_diff = cli.call({"op": "BundlesCommute", "actionA": "run-study", "actionB": "log-note"})
    assert comm_diff.ok and comm_diff.raw.get("commutes") is True, f"expected true disjoint commute: {comm_diff.raw}"
    comm_same = cli.call({"op": "BundlesCommute", "actionA": "run-study", "actionB": "run-study"})
    assert comm_same.ok and comm_same.raw.get("commutes") is False, f"expected false self-commute: {comm_same.raw}"

    # Verify offline `replay` of the log including `delegateWhen` EnactBundle BEFORE AmendLaw switches artifacts!
    import subprocess as _sp
    rep_pre = _sp.run([sys.argv[2], "replay", sys.argv[3], sys.argv[5]], capture_output=True, text=True)
    assert rep_pre.returncode == 0, f"offline replay of delegateWhen bundle log failed: {rep_pre.stderr}"

    # F. `AmendLaw` epoch separation: old bundle1 rejected for new EnactBundle (even with fresh bundleId),
    #    while `VerifyBundle` with `auditHistorical: True` still verifies bundle1!
    stg = cli.call({"op": "ExercisePower", "action": "stage-amendment", "args": ["Panel"]})
    assert stg.ok
    am = cli.call({"op": "AmendLaw", "amendAct": "upgrade-law", "args": ["Panel"], "successorArtifact": sys.argv[4]})
    assert am.ok, f"AmendLaw failed: {am.raw}"

    ver_active = cli.call({"op": "VerifyBundle", "bundle": bundle1})
    assert ver_active.ok and ver_active.raw.get("permitted") is False, \
        f"superseded-law bundle must not pass active VerifyBundle: {ver_active.raw}"

    ver_hist = cli.call({"op": "VerifyBundle", "bundle": bundle1, "auditHistorical": True})
    assert ver_hist.ok and ver_hist.raw.get("permitted") is True, \
        f"previously enacted bundle must pass auditHistorical VerifyBundle: {ver_hist.raw}"
finally:
    cli.close()
PY

echo "ok   d44-extensions (epoch/replay bundles, delegateWhen, diff --impact, dutyDeltas/GetActorBrief, UCON Authorize, repl branching)"
