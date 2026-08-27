#!/usr/bin/env python3
"""Ask stale E40 sessions to commit their current artifacts and terminate."""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sorry_pipeline as pipeline

SESSION_IDS = [
    "7933620650000174648",
    "8205093337022620311",
    "3652215230464516066",
    "17416315947121350819",
    "10231652485512067486",
    "5678410110478816212",
]

FINALIZE = (
    "The E40 campaign budget ended many hours ago. Do not start a new search. "
    "Commit any already-created useful artifacts, keep exact/numerical claims "
    "clearly separated, and finish the session now with your current result."
)


for sid in SESSION_IDS:
    code, body = pipeline.api("GET", f"/sessions/{sid}")
    state = (body or {}).get("state", "UNKNOWN")
    action = "none"
    if state == "AWAITING_PLAN_APPROVAL":
        trigger = pipeline.latest_trigger(sid, state)
        if trigger:
            code, _ = pipeline.api(
                "POST", f"/sessions/{sid}:approvePlan", body={})
            action = f"approvePlan:{code}"
    elif state == "AWAITING_USER_FEEDBACK":
        code, _ = pipeline.api("POST", f"/sessions/{sid}:sendMessage",
                               body={"prompt": FINALIZE})
        action = f"finalizeMessage:{code}"
    print(f"{sid} state={state} action={action}", flush=True)
