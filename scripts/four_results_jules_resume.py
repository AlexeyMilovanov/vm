#!/usr/bin/env python3
"""Resume and audit the existing four-results Jules wave."""

import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path.home() / "vm" / "scripts"))
import sorry_pipeline as pipeline

HOME = Path.home()
pipeline.ROOT = HOME / "vm"
pipeline.WORK = HOME / "vm-four-results-work"
pipeline.PUSH = HOME / "vm-four-results-push"
pipeline.PULLC = HOME / "vm-four-results-jules-pull"
pipeline.CTRL = pipeline.ROOT / "pipeline"
pipeline.RUNS = pipeline.ROOT / "pipeline_runs"
pipeline.SEP_DIR = "HeadComplexity"
pipeline.ALLOWED_PATCH_RE = re.compile(
    r"^(HeadComplexity(?:\.lean|/)|PROOFS\.md$|PROGRESS\.md$|"
    r"sorry_queue\.json$|BLOCKER_[A-Za-z0-9_']+\.md$|hints/)"
)
pipeline.JULES_PHASE_CAP = 6 * 3600
pipeline.JULES_SESSION_BUDGET = 45 * 60
pipeline.JULES_POLL = 30
pipeline.JULES_BATCH = 23
pipeline.BUILD_TIMEOUT = 1800
pipeline.JULES_NUDGE = (
    "Proceed with your best judgment. Preserve the assigned statement exactly. "
    "If blocked, commit every honest fully proved helper and leave the target "
    "sorry; do not weaken any statement."
)


def lightweight_audit(cwd):
    hits = pipeline.forbidden_scan(cwd)
    if hits:
        return False, "forbidden constructs: " + "; ".join(hits[:10])
    ok, tail = pipeline.lake_build(cwd, "HeadComplexity")
    if not ok:
        return False, "HeadComplexity build failed:\n" + tail
    ok, tail = pipeline.smoke_build(cwd)
    if not ok:
        return False, "statement freeze violated:\n" + tail
    return True, "ok"


pipeline.full_audit = lightweight_audit

def module_audit(cwd):
    hits = pipeline.forbidden_scan(cwd)
    if hits:
        return False, "forbidden constructs: " + "; ".join(hits[:10])
    changed = pipeline.sh(
        ["git", "diff", "--name-only", "HEAD"], cwd=cwd, timeout=60
    ).stdout.splitlines()
    lean_paths = [
        path for path in changed
        if path.startswith("HeadComplexity/") and path.endswith(".lean")
    ]
    if not lean_paths:
        return False, "patch changes no HeadComplexity Lean module"
    for path in lean_paths:
        target = path[:-5].replace("/", ".")
        ok, tail = pipeline.lake_build(cwd, target)
        if not ok:
            return False, f"{target} build failed:\n" + tail
    ok, tail = pipeline.smoke_build(cwd)
    if not ok:
        return False, "statement freeze violated:\n" + tail
    return True, "ok"


pipeline.full_audit = module_audit

source = (
    pipeline.RUNS / "four_results_20260827T182143Z" /
    "jules" / "sessions.json"
)
raw = json.loads(source.read_text())
by_name = {name: sid for sid, name in raw.items()}
entries = pipeline.validated_entries(
    pipeline.ROOT, ("jules_ready", "hard")
)
entries = [entry for entry in entries if entry["name"] in by_name and not pipeline.target_closed(pipeline.ROOT, entry)]
if not entries:
    raise SystemExit("no open targets from the first Jules wave")


def existing_session(entry, _base_sha, _logdir):
    return by_name[entry["name"]]


pipeline.jules_submit = existing_session
stamp = datetime.now(timezone.utc).strftime("four_results_resume_%Y%m%dT%H%M%SZ")
iter_dir = pipeline.RUNS / stamp
iter_dir.mkdir(parents=True, exist_ok=False)
pipeline.log(f"resuming first Jules wave: {len(entries)} open targets")
pipeline.jules_phase(entries, "existing-first-wave", iter_dir)
