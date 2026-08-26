#!/usr/bin/env python3
"""Submit and babysit all non-foundational TypicalLogCloseness Jules tasks.

This process deliberately does not apply patches.  It only maximizes prover
parallelism, approves plans, answers routine feedback, and records terminal
sessions.  The main audited wave integrates patches after its foundational
definitions have settled.
"""

import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path.home() / "hstar-separations-lean" / "scripts"))
import sorry_pipeline as pipeline

BASE_STAGE = {
    "log_pos_of_two_le", "powerBlockSize_le_self", "starCoord_card",
    "cubeSplitEquiv", "coordMismatchForm_eval", "paramIndexEquiv",
    "boundedTopologyFintype", "cubeIndexEquiv_inj",
}
OUT = pipeline.RUNS / "typical_log_closeness" / "fanout_all_remaining"
OUT.mkdir(parents=True, exist_ok=True)


def prompt(entry, base_sha):
    return f"""Prove exactly one Lean 4.31 declaration in AlexeyMilovanov/vm.

Base commit: {base_sha} on main. Check git rev-parse HEAD first; on mismatch
reply exactly BASE_COMMIT_MISMATCH and stop.

Target: {entry['name']} in {entry['file']}. Other sorry declarations belong to
parallel sessions. Preserve every existing statement exactly and remove only
the target sorry. You may add honest, fully proved private helpers immediately
above it. Do not use sorry, admit, axiom, unsafe, native_decide,
maxHeartbeats, or maxRecDepth in the completed proof. Run lake build.

Mathematical route:
{entry.get('note', '')}

Some dependencies are being proved in parallel. You may use their exact public
statements, but never assume a stronger statement and never edit them. If the
target genuinely requires unfolding a dependency whose body is still sorry,
leave the target sorry and commit only useful fully proved private helpers.
Report whether the target is completely sorry-free and list changed files."""


def save(sessions):
    data = {
        sid: {
            "name": info["entry"]["name"],
            "state": info["state"],
            "nudged": info["nudged"],
        }
        for sid, info in sessions.items()
    }
    (OUT / "sessions.json").write_text(json.dumps(data, indent=2))


if len(sys.argv) != 2:
    raise SystemExit("usage: typical_jules_fanout.py BASE_SHA")
base_sha = sys.argv[1]
pipeline.jules_prompt = prompt
entries = [
    entry for entry in pipeline.validated_entries(
        pipeline.ROOT, ("jules_ready", "hard"))
    if entry["name"] not in BASE_STAGE
]
pipeline.log(f"TypicalLogCloseness fanout: submitting {len(entries)} targets")
sessions = {}
for entry in entries:
    sid = pipeline.jules_submit(entry, base_sha, OUT)
    if sid:
        sessions[sid] = {
            "entry": entry, "state": "submitted", "nudged": 0,
            "acted": set(), "terminal": False,
        }
        pipeline.log(f"fanout submitted {entry['name']} session={sid}")
        save(sessions)
    else:
        pipeline.log(f"fanout submit FAILED for {entry['name']}")
    time.sleep(5)

deadline = time.time() + 6 * 3600
while time.time() < deadline and any(not i["terminal"] for i in sessions.values()):
    for sid, info in sessions.items():
        if info["terminal"]:
            continue
        status, body = pipeline.api("GET", f"/sessions/{sid}")
        state = (body or {}).get("state", "UNKNOWN")
        info["state"] = state
        if state in {"COMPLETED", "FAILED"}:
            info["terminal"] = True
            pipeline.log(f"fanout terminal {info['entry']['name']}: {state}")
        elif state == "AWAITING_PLAN_APPROVAL":
            trigger = pipeline.latest_trigger(sid, state)
            if trigger and trigger not in info["acted"]:
                code, _ = pipeline.api("POST", f"/sessions/{sid}:approvePlan", body={})
                info["acted"].add(trigger)
                pipeline.log(
                    f"fanout approved {info['entry']['name']} plan (http {code})")
        elif state == "AWAITING_USER_FEEDBACK":
            trigger = pipeline.latest_trigger(sid, state)
            if trigger and trigger not in info["acted"] and info["nudged"] < 2:
                pipeline.api(
                    "POST", f"/sessions/{sid}:sendMessage",
                    body={"prompt": pipeline.JULES_NUDGE})
                info["acted"].add(trigger)
                info["nudged"] += 1
                pipeline.log(
                    f"fanout nudged {info['entry']['name']} ({info['nudged']}/2)")
    save(sessions)
    time.sleep(30)

save(sessions)
pipeline.log(
    "TypicalLogCloseness fanout monitor finished at "
    + datetime.now(timezone.utc).isoformat())
