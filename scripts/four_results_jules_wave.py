#!/usr/bin/env python3
"""Run the audited Jules fanout for the four new formalization skeletons.

One remote session owns one declaration.  The shared pipeline approves plans,
answers routine questions, harvests patches, integrates them one at a time,
and accepts a patch only after a sequential Lean build and semantic review.
"""

import re
from datetime import datetime, timezone
from pathlib import Path

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
pipeline.JULES_PHASE_CAP = 8 * 3600
pipeline.JULES_SESSION_BUDGET = 75 * 60
pipeline.JULES_POLL = 30
pipeline.JULES_BATCH = 23
pipeline.BUILD_TIMEOUT = 3600
pipeline.JULES_NUDGE = (
    "Proceed with your best judgment. Preserve the assigned statement "
    "exactly, use the detailed queue note and neighbouring declarations, "
    "and run the build. If blocked, commit only honest fully proved helper "
    "lemmas and leave the target sorry."
)


def prompt(entry, base_sha):
    return f"""Prove exactly one Lean 4.31 declaration in AlexeyMilovanov/vm.

Base commit: {base_sha} on main. First check git rev-parse HEAD. If it differs,
reply exactly BASE_COMMIT_MISMATCH and stop.

Target: {entry['name']} in {entry['file']}. It contains exactly one sorry.
The other sorry declarations belong to parallel Jules sessions.

Audited mathematical route and local API hints:
{entry.get('note', '')}

Rules:
1. Preserve every existing statement exactly and remove only the target sorry.
   You may add honest fully proved private helpers immediately above it.
2. Do not edit another existing declaration. Do not weaken hypotheses or the
   conclusion. Do not rename canonical POIC2 back to the relaxed invariant.
3. Forbidden: sorry in a claimed completed target, admit, axiom, unsafe,
   native_decide, set_option maxHeartbeats, and set_option maxRecDepth.
4. Inspect all neighbouring declarations and reuse repository/mathlib lemmas.
   Exact public statements of parallel targets may be used as dependencies.
5. Run `lake -Kjobs=1 build {entry['file']}` or the corresponding module.
   Warnings about other assigned sorries are expected.
6. If the complete proof is out of reach, keep the target sorry and commit
   only useful fully proved helpers. If the statement is false, add a precise
   BLOCKER_{entry['name']}.md instead of changing the theorem.

In the final report say whether the target is completely sorry-free and list
all changed files."""


pipeline.jules_prompt = prompt
entries = pipeline.validated_entries(
    pipeline.ROOT, ("jules_ready", "hard"))
if len(entries) != 23:
    names = [entry["name"] for entry in entries]
    raise SystemExit(f"expected 23 validated targets, found {len(entries)}: {names}")

pipeline.CTRL.mkdir(exist_ok=True)
(pipeline.ROOT / "hints").mkdir(exist_ok=True)
stamp = datetime.now(timezone.utc).strftime("four_results_%Y%m%dT%H%M%SZ")
iter_dir = pipeline.RUNS / stamp
iter_dir.mkdir(parents=True, exist_ok=False)
pipeline.log(f"four-results Jules wave: submitting {len(entries)} targets")
sha = pipeline.push_root_to_github(
    f"four-results Jules wave: {len(entries)} verified sorry leaves")
pipeline.jules_phase(entries, sha, iter_dir)
