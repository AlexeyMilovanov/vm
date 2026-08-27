#!/usr/bin/env python3
"""Submit the second four-results Jules wave without local integration builds."""

import json
import re
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

import sorry_pipeline as pipeline

ROOT = Path.home() / "vm"
pipeline.ROOT = ROOT
pipeline.CTRL = ROOT / "pipeline"
pipeline.RUNS = ROOT / "pipeline_runs"
pipeline.ALLOWED_PATCH_RE = re.compile(
    r"^(HeadComplexity(?:\.lean|/)|PROOFS\.md$|PROGRESS\.md$|"
    r"BLOCKER_[A-Za-z0-9_']+\.md$|hints/)"
)

ENTRIES = [
    {
        "name": "continuousAt_perturbationEval_zero",
        "file": "HeadComplexity/TypicalLogCloseness/CanonicalPOIC.lean",
        "note": (
            "Pointwise continuity at epsilon=0. Unfold perturbationEval. "
            "Finite sums/products of affine functions of epsilon are continuous. "
            "For every denominator factor, its value at 0 is the original "
            "strictly positive denominator evaluation, hence nonzero; use "
            "ContinuousAt.div with the finite product nonzero at 0."
        ),
    },
    {
        "name": "exists_positive_parameter_preserving_sign",
        "file": "HeadComplexity/TypicalLogCloseness/CanonicalPOIC.lean",
        "note": (
            "Cube n is finite. For each x, continuity and g 0 x != 0 imply "
            "g epsilon x * g 0 x remains positive in a neighborhood of 0. "
            "Intersect finitely many neighborhoods, then choose a strictly "
            "positive epsilon in the resulting neighborhood. Finset.univ and "
            "a minimum radius are both acceptable."
        ),
    },
    {
        "name": "hasSpanningBank_zero",
        "file": "HeadComplexity/TypicalLogCloseness/Bank.lean",
        "note": (
            "Use one pole positiveDirection 0. Cube 0 is a singleton. For an "
            "arbitrary table v choose the constant affine numerator equal to "
            "v at the unique cube point; the denominator evaluates to 1."
        ),
    },
    {
        "name": "hasSpanningBank_one_totality",
        "file": "HeadComplexity/TypicalLogCloseness/Bank.lean",
        "note": (
            "There is already a fully proved private theorem hasSpanningBank_one "
            "later in this same file. Because forward references are unavailable, "
            "copy/adapt that exact proof above; do not change either statement."
        ),
    },
    {
        "name": "hasSpanningBank_of_two_le",
        "file": "HeadComplexity/TypicalLogCloseness/Bank.lean",
        "note": (
            "Let L=powerBlockLocalization n hn. Obtain T,hpositive,hcleared from "
            "exists_legal_fullRank_bank L; set B=legalPath L T. StrictAdmissible "
            "comes from hpositive. Use fractional_det_ne_zero followed by "
            "fixedBank_spans for every real table v, and package HasSpanningBank."
        ),
    },
    {
        "name": "exists_fracAtom_eval_eq_of_strictAdmissible",
        "file": "HeadComplexity/TypicalLogCloseness/Bank.lean",
        "note": (
            "Positive slopes are exactly exists_fracAtom_eval_eq. For strictly "
            "negative slopes use the first-wave partial patch saved in "
            "hints/HStar_le_Bank.diff: choose 0<d<1, alpha=1-d, "
            "rho_i=-B.linear_i/d, and solve gamma, eta, m with delta=0. "
            "Repair only Lean algebra/API errors; the construction is audited."
        ),
    },
    {
        "name": "f8_quadratic_mixed_negative",
        "file": "HeadComplexity/Separations/EightBitHammingThreshold.lean",
        "note": (
            "Follow paper Theorem 189 Lemma 2 exactly. Use checkerboard second "
            "differences to get the fourteen certified direction-pair inequalities, "
            "then simultaneous signed-coordinate permutations. Sort an arbitrary "
            "nonzero z by absolute value and expand it in prefix vectors p1..p4. "
            "Use the q2,q3,q4 and r2,r3,r4 identities to control the sole p1,p4 "
            "cross term. The source proof is "
            "/home/lesha/rs-takehome-results/source/rs-takehome/theorems/"
            "06_strict_separations/189_eight_bit_hamming_threshold_strict_separation.md."
        ),
    },
    {
        "name": "offDiag_sum_bound",
        "file": "HeadComplexity/Separations/EightBitHammingThreshold.lean",
        "note": (
            "This is the single extracted algebraic core of the column-max theorem; "
            "all picker, quad_expand, and final contradiction code around it already "
            "compiles. The old failed proof is in hints/columnMax_spectral_inequality.diff. "
            "Do not repeat its invalid final linear_combination. Prove the bound via "
            "the paper Lemma 5 squared-distance cone/edge-allocation argument, or "
            "repair the finite four-dimensional inequality with explicit nlinarith."
        ),
    },
    {
        "name": "two_heads_yield_f8NormalizedSystem",
        "file": "HeadComplexity/Separations/EightBitHammingThreshold.lean",
        "note": (
            "Clearing, degree, sign, multilinearization, and negative curvature are "
            "now already proved immediately above. Continue from phi,c,hsign,hneg "
            "with paper Lemmas 3-4: build A,D,C,B factor map, prove denominators "
            "nonconstant from nonsingular mixed curvature, define Phi,Delta,C0,E,t, "
            "then U=Delta*C0,V=Delta*E,w=Delta*t,mu=Delta^-1*lambda and fill exactly "
            "the F8NormalizedSystem fields. Do not weaken the structure."
        ),
    },
    {
        "name": "not_nonempty_f8NormalizedSystem",
        "file": "HeadComplexity/Separations/EightBitHammingThreshold.lean",
        "note": (
            "Follow paper Lemma 6. First prove the contradiction when every mu_i "
            "is nonzero using signs, contraction inequalities, and "
            "columnMax_spectral_inequality. Then remove zero coordinates by a small "
            "null-cone perturbation; strict slope/intercept inequalities persist. "
            "The trace_plus_two_sum helper is already present. Add honest private "
            "helpers if needed, leaving only this assigned target changed."
        ),
    },
]


def prompt(entry, base_sha):
    return f"""Prove exactly one Lean 4.31 declaration in AlexeyMilovanov/vm.

Base commit: {base_sha} on main. Verify git rev-parse HEAD first.
Target: {entry['name']} in {entry['file']}.

Route and local API hints:
{entry['note']}

Preserve the statement exactly. Remove only this target's sorry. Other sorries
belong to parallel sessions and may be used as declared theorems. You may add
fully proved private helpers immediately above the target. Forbidden: sorry in
a claimed completion, admit, axiom, unsafe, native_decide, maxHeartbeats, and
maxRecDepth. Run a one-job build of the target module. If blocked, keep the
target sorry and commit only honest proved helpers. Report changed files and
whether the target is completely sorry-free."""


pipeline.jules_prompt = prompt
base_sha = subprocess.check_output(
    ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
stamp = datetime.now(timezone.utc).strftime("four_results_wave2_%Y%m%dT%H%M%SZ")
jdir = ROOT / "pipeline_runs" / stamp / "jules"
jdir.mkdir(parents=True)
sessions = {}
for entry in ENTRIES:
    if pipeline.target_closed(ROOT, entry):
        raise SystemExit(f"target unexpectedly closed before submit: {entry['name']}")
    sid = pipeline.jules_submit(entry, base_sha, jdir)
    if sid:
        sessions[sid] = entry["name"]
        pipeline.log(f"wave2 submitted {entry['name']} session={sid}")
    else:
        pipeline.log(f"wave2 submit FAILED for {entry['name']}")
    time.sleep(5)
(jdir / "sessions.json").write_text(json.dumps(sessions, indent=2))
print(json.dumps({"base": base_sha, "run": str(jdir.parent), "sessions": sessions},
                 indent=2))
