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

# Definitions are deliberately completed before proofs which unfold them.
# Within each dependency stage, every target is assigned to its own concurrent
# Jules session.
STAGES = {
    1: {
        "log_pos_of_two_le", "powerBlockSize_le_self", "starCoord_card",
        "cubeSplitEquiv", "coordMismatchForm_eval", "paramIndexEquiv",
        "boundedTopologyFintype", "cubeIndexEquiv_inj",
    },
    2: {
        "starCoordEquiv", "starCenter_card", "certToPoint",
        "boundedTopology_card_le", "represented_truthTables_embedding",
        "warren_pattern_card_nat_le", "topology_param_degree_le",
        "constant_sublevel_card_le",
    },
    3: {
        "powerBlockGroupEquiv", "denomMvPoly", "numMvPoly",
        "exp_ineq_topologyCountBound", "exp_ineq_warrenTerm",
    },
    4: {
        "powerBlockPartition", "denomMvPoly_eval", "numMvPoly_eval",
        "denomMvPoly_totalDegree_le", "numMvPoly_totalDegree_le",
        "sublevel_exp_bound_combination",
    },
    5: {"powerBlockEll", "powerBlockLagrange", "clearedTermMvPoly"},
    6: {
        "powerBlockEll_zero_iff", "powerBlockLagrange_delta",
        "clearedScoreMvPoly",
    },
    7: {"clearedScoreMvPoly_eval", "clearedScoreMvPoly_totalDegree_le"},
    8: {"strict_sign_transfer", "fixedTopology_warren_model_helper"},
    9: {"truthTables_per_topology_card_le", "nonconstant_sublevel_card_le"},
    10: {"poic2_sublevel_card_le_helper"},
}

if len(sys.argv) != 2 or not sys.argv[1].isdigit():
    raise SystemExit("usage: typical_jules_wave.py STAGE (1..10)")
stage = int(sys.argv[1])
if stage not in STAGES:
    raise SystemExit(f"unknown stage {stage}; expected 1..10")
all_ready = pipeline.validated_entries(
    pipeline.ROOT, ("jules_ready", "hard"))
ready = [entry for entry in all_ready if entry["name"] in STAGES[stage]]
missing = STAGES[stage] - {entry["name"] for entry in ready}
if missing:
    raise SystemExit(f"stage {stage} queue entries missing: {sorted(missing)}")
wave = f"stage_{stage:02d}"
pipeline.log(f"typical Jules wave {wave}: {len(ready)} targets")
sha = pipeline.push_root_to_github(
    f"TypicalLogCloseness Jules wave {wave}: {len(ready)} leaves")
iter_dir = pipeline.RUNS / "typical_log_closeness" / wave
iter_dir.mkdir(parents=True, exist_ok=True)
pipeline.jules_phase(ready, sha, iter_dir)
