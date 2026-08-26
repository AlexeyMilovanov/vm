#!/usr/bin/env python3
"""Audit/integrate fanout Jules patches, or retry every still-open target."""

import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path.home() / "hstar-separations-lean" / "scripts"))
import sorry_pipeline as pipeline

pipeline.SEP_DIR = "HeadComplexity/TypicalLogCloseness"
pipeline.ALLOWED_PATCH_RE = re.compile(
    r"^(HeadComplexity/TypicalLogCloseness(?:\.lean|/)|"
    r"PROOFS\.md$|PROGRESS\.md$|sorry_queue\.json$|"
    r"BLOCKER_[A-Za-z0-9_']+\.md$|hints/)"
)
pipeline.JULES_PHASE_CAP = 6 * 3600
pipeline.JULES_SESSION_BUDGET = 45 * 60
pipeline.JULES_POLL = 30
pipeline.JULES_BATCH = 10
pipeline.JULES_NUDGE = (
    "Proceed with your best judgment. Prove only the assigned declaration, "
    "preserve every statement exactly, use the now-proved neighbouring "
    "definitions and lemmas, and run lake build. If blocked, commit only "
    "honest fully-proved private helpers and leave the target sorry."
)


def prompt(entry, base_sha):
    return f"""Prove exactly one Lean 4.31 declaration in AlexeyMilovanov/vm.

Base commit: {base_sha} on main. Check git rev-parse HEAD first; on mismatch
reply exactly BASE_COMMIT_MISMATCH and stop.

Target: {entry['name']} in {entry['file']}. Preserve its statement exactly and
remove only its sorry. Other sorry declarations belong to parallel sessions.
You may add fully proved private helpers immediately above the target. Forbidden:
sorry in the completed target, admit, axiom, unsafe, native_decide,
maxHeartbeats, and maxRecDepth. Run lake build.

Mathematical route:
{entry.get('note', '')}

Inspect and use all neighbouring declarations already proved on this base. If
blocked, keep the target sorry and commit only sound fully proved helpers."""


pipeline.jules_prompt = prompt
queue = pipeline.validated_entries(pipeline.ROOT, ("jules_ready", "hard"))

if len(sys.argv) != 2 or sys.argv[1] not in {"fanout", "retry"}:
    raise SystemExit("usage: typical_jules_integrate.py fanout|retry")
mode = sys.argv[1]

if mode == "fanout":
    fanout_file = (
        pipeline.RUNS / "typical_log_closeness" /
        "fanout_all_remaining" / "sessions.json")
    raw = json.loads(fanout_file.read_text())
    by_name = {info["name"]: sid for sid, info in raw.items()}
    entries = [entry for entry in queue if entry["name"] in by_name]
    if len(entries) != 32:
        raise SystemExit(f"expected 32 fanout sessions, found {len(entries)}")
    base_targets = [entry for entry in queue if entry["name"] not in by_name]
    still_open = [
        entry["name"] for entry in base_targets
        if not pipeline.target_closed(pipeline.ROOT, entry)
    ]
    if still_open:
        raise SystemExit(
            "foundational wave is not integrated yet: " + ", ".join(still_open))

    def existing_session(entry, _base_sha, _logdir):
        return by_name[entry["name"]]

    pipeline.jules_submit = existing_session
    iter_dir = (
        pipeline.RUNS / "typical_log_closeness" / "fanout_integration")
    iter_dir.mkdir(parents=True, exist_ok=True)
    pipeline.jules_phase(entries, "fanout-existing-sessions", iter_dir)
else:
    entries = [
        entry for entry in queue
        if not pipeline.target_closed(pipeline.ROOT, entry)
    ]
    if not entries:
        raise SystemExit("no open TypicalLogCloseness targets")
    round_no = 1
    while (pipeline.RUNS / "typical_log_closeness" /
           f"retry_{round_no:02d}").exists():
        round_no += 1
    wave = f"retry_{round_no:02d}"
    sha = pipeline.push_root_to_github(
        f"TypicalLogCloseness {wave}: {len(entries)} remaining leaves")
    iter_dir = pipeline.RUNS / "typical_log_closeness" / wave
    iter_dir.mkdir(parents=True, exist_ok=True)
    pipeline.jules_phase(entries, sha, iter_dir)
