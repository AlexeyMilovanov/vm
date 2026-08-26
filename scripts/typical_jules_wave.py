#!/usr/bin/env python3
"""Run one audited Jules wave for TypicalLogCloseness.

Every queue entry owns exactly one declaration containing sorry.  Sessions are
submitted concurrently, plans and routine feedback are handled by the shared
pipeline, and only patches passing the full Lean build and semantic review are
merged.
"""

import re
import sys
from datetime import datetime, timezone
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
    "preserve every statement exactly, follow its adjacent doc comment and "
    "queue hint, and run the full Lean build. If blocked, commit only honest "
    "fully-proved private helpers and leave the target sorry."
)


def typical_prompt(entry, base_sha):
    return f"""Prove exactly one Lean 4.31 declaration in AlexeyMilovanov/vm.

Base commit: {base_sha} on main.  First check git rev-parse HEAD.  If it differs,
reply exactly BASE_COMMIT_MISMATCH and stop.

Target: {entry['name']} in {entry['file']}.  It currently contains exactly one
sorry.  Other declarations containing sorry belong to parallel sessions.

Mathematical route:
{entry.get('note', '')}

Rules:
1. Remove only the target sorry.  You may add fully proved private helpers
   immediately above the target, but do not edit any other declaration or any
   existing statement.
2. Forbidden: sorry in the completed target, admit, axiom, unsafe,
   native_decide, set_option maxHeartbeats, and set_option maxRecDepth.
3. Reuse existing Mathlib and repository lemmas.  In particular inspect the
   adjacent helper declarations and HeadComplexity/Separations/NDISJ.lean when
   working with multivariate polynomials and cleared denominators.
4. Run lake build.  Warnings about other sorries are expected.
5. If the full proof is out of reach, keep the target sorry and contribute only
   sound, fully proved private helpers.  Never weaken the statement.

Report whether the target is completely sorry-free and list changed files."""


pipeline.jules_prompt = typical_prompt
ready = pipeline.validated_entries(pipeline.ROOT, ("jules_ready", "hard"))
wave = sys.argv[1] if len(sys.argv) > 1 else datetime.now(
    timezone.utc).strftime("wave_%Y%m%dT%H%M%SZ")
pipeline.log(f"typical Jules wave {wave}: {len(ready)} targets")
sha = pipeline.push_root_to_github(
    f"TypicalLogCloseness Jules wave {wave}: {len(ready)} leaves")
