#!/usr/bin/env python3
"""Submit and monitor the forty two-hour POIC2 E-profile Jules sessions."""

from __future__ import annotations

import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


HOME = Path.home()
REPO = HOME / "vm-push"
CAMPAIGN = REPO / "campaigns" / "poic2_e40"
HARVEST = HOME / "e40_jules_harvest"
PIPELINE_SCRIPTS = HOME / "hstar-separations-lean" / "scripts"
sys.path.insert(0, str(PIPELINE_SCRIPTS))
import sorry_pipeline as pipeline


SESSION_BUDGET = 2 * 3600
PHASE_GRACE = 20 * 60
POLL = 30
NUDGE = (
    "Proceed autonomously. This is a two-hour experimental research session, "
    "not a one-shot coding task. Do not stop after one failed numerical run; "
    "inspect the diagnostics, change the method, and continue. Save intermediate "
    "code, checkpoints, and timestamped research_log entries. Never infer an "
    "exact lower bound from solver failure."
)


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def log(message: str) -> None:
    line = f"[{now()}] {message}"
    print(line, flush=True)
    with (HARVEST / "monitor.log").open("a") as fh:
        fh.write(line + "\n")


def make_prompt(case, base_sha: str) -> str:
    cid = case["case_id"]
    rel = f"campaigns/poic2_e40/cases/{cid}"
    return f"""Work for up to two hours as an autonomous experimental
mathematician/programmer on exactly one POIC_2 versus H* case in the GitHub
repository {pipeline.GH_REPO}.

Base commit: {base_sha} on main.  First run `git rev-parse HEAD`.  If it differs,
reply exactly BASE_COMMIT_MISMATCH and stop.

Your case is `{cid}`.  Read `{rel}/TASK.md`, `{rel}/input.json`, the campaign
README, and the read-only material under `campaigns/poic2_e40/common/`.

You own only `{rel}/`.  Do not modify common files, Lean files, repository
configuration, or another case.  You may create local solvers, exact verifiers,
JSON results, checkpoints, and reports inside your case directory.  If you find
a generally useful common improvement, save it as `{rel}/proposed_common.patch`
instead of editing common code.

This is an adaptive research task, not a single prescribed computation.  Start
from the supplied baselines, inspect their results, correct or replace methods
when justified, and try genuinely different POIC budget-three topologies and H3
orientation cells.  Unless an exact decisive certificate is found, do not stop
after the first failed attempt: use the available time, ideally at least 100
minutes if the platform permits.  Append timestamped intermediate findings to
`{rel}/research_log.md` frequently so a timeout cannot erase the work.

The exact current fact is only an axis/infinity obstruction for the E profile.
No POIC_2 <= 3 source is known.  Numerical failure proves neither POIC_2 > 3 nor
H* > 3.  A positive claim must include all coefficients and an independent
exact-arithmetic full-cube verifier.  Run
`python3 campaigns/poic2_e40/common/validate_case.py {rel}` before finishing.

Commit every useful artifact.  The final report must separate exact facts,
numerical evidence, and conjectural ideas, and state the final result.json
status explicitly.
"""


def save(sessions) -> None:
    serial = {}
    for sid, info in sessions.items():
        serial[sid] = {
            "case_id": info["case"]["case_id"],
            "state": info["state"],
            "submitted_at": info["submitted_at"],
            "nudged": info["nudged"],
            "pulled": info["pulled"],
            "patch_file": info.get("patch_file"),
            "structural_status": info.get("structural_status"),
        }
    (HARVEST / "sessions.json").write_text(json.dumps(serial, indent=2) + "\n")


def allowed_patch(patch: str, case_id: str):
    paths = pipeline.patch_paths(patch)
    prefix = f"campaigns/poic2_e40/cases/{case_id}/"
    if not paths:
        return False, "empty patch"
    bad = [p for p in paths if not p.startswith(prefix)]
    if bad:
        return False, "disallowed paths: " + repr(bad[:8])
    return True, "ok"


def pull(sid: str, info, reason: str) -> None:
    if info["pulled"]:
        return
    cid = info["case"]["case_id"]
    patch = pipeline.jules_pull(sid)
    pfile = HARVEST / f"{cid}.patch"
    if patch:
        pfile.write_text(patch)
        ok, why = allowed_patch(patch, cid)
        info["structural_status"] = ("PASS: " if ok else "REJECT: ") + why
        info["patch_file"] = str(pfile)
        log(f"pulled {cid} reason={reason} bytes={len(patch)} structural={info['structural_status']}")
    else:
        info["structural_status"] = "EMPTY"
        log(f"pulled {cid} reason={reason}: no patch")
    info["pulled"] = True


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: e40_jules_fanout.py BASE_SHA")
    base_sha = sys.argv[1]
    assert (REPO / ".git").exists()
    assert CAMPAIGN.exists()
    manifest = json.loads((CAMPAIGN / "manifest.json").read_text())
    cases = manifest["cases"]
    assert manifest["case_count"] == 40 and len(cases) == 40

    HARVEST.mkdir(exist_ok=True)
    (HARVEST / "base_sha.txt").write_text(base_sha + "\n")
    (HARVEST / "manifest_snapshot.json").write_text(
        json.dumps(manifest, indent=2) + "\n")

    pipeline.jules_prompt = lambda entry, sha: make_prompt(entry["case"], sha)
    sessions = {}
    log(f"submitting 40 E-profile sessions base={base_sha} budget=2h")
    for case in cases:
        entry = {"name": case["case_id"], "file": case["path"], "case": case}
        sid = pipeline.jules_submit(entry, base_sha, HARVEST)
        if sid:
            sessions[sid] = {
                "case": case,
                "t0": time.time(),
                "submitted_at": now(),
                "state": "SUBMITTED",
                "acted": set(),
                "nudged": 0,
                "pulled": False,
            }
            log(f"submitted {case['case_id']} session={sid}")
            save(sessions)
        else:
            log(f"SUBMIT_FAILED {case['case_id']}")
        time.sleep(5)

    deadline = time.time() + SESSION_BUDGET + PHASE_GRACE
    while time.time() < deadline and any(not i["pulled"] for i in sessions.values()):
        for sid, info in sessions.items():
            if info["pulled"]:
                continue
            age = time.time() - info["t0"]
            _, body = pipeline.api("GET", f"/sessions/{sid}")
            state = (body or {}).get("state", "UNKNOWN")
            if state != info["state"]:
                info["state"] = state
                log(f"state {info['case']['case_id']}={state} age={age/60:.1f}m")
            if state in {"COMPLETED", "FAILED"}:
                pull(sid, info, state.lower())
            elif age >= SESSION_BUDGET:
                pull(sid, info, "two-hour-budget")
            elif state == "AWAITING_PLAN_APPROVAL":
                trig = pipeline.latest_trigger(sid, state)
                if trig and trig not in info["acted"]:
                    code, _ = pipeline.api("POST", f"/sessions/{sid}:approvePlan", body={})
                    info["acted"].add(trig)
                    log(f"approved {info['case']['case_id']} http={code}")
            elif state == "AWAITING_USER_FEEDBACK":
                trig = pipeline.latest_trigger(sid, state)
                if trig and trig not in info["acted"] and info["nudged"] < 3:
                    pipeline.api("POST", f"/sessions/{sid}:sendMessage", body={"prompt": NUDGE})
                    info["acted"].add(trig)
                    info["nudged"] += 1
                    log(f"nudged {info['case']['case_id']} {info['nudged']}/3")
        save(sessions)
        time.sleep(POLL)

    for sid, info in sessions.items():
        if not info["pulled"]:
            pull(sid, info, "phase-grace-timeout")
    save(sessions)
    log("monitor complete")


if __name__ == "__main__":
    main()
