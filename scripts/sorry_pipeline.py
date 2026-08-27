#!/usr/bin/env python3
"""Sorry-closing pipeline for hstar-separations-lean.

Per iteration:
  local chain  opus -> gemini(do) -> gemini(check) -> codex -> gemini(do)
               -> gemini(check) -> opus(final)
  gate         >= MIN_QUEUE jules-ready leaves in sorry_queue.json
  push         to github.com/AlexeyMilovanov/vm main
  jules        one session per leaf, 2h budget each, canned unblocking,
               plan auto-approval, escalation files to ~/jules_needs_attention
  review       structural gates + build + gemini semantic verdict; accepted
               patches merged into ROOT and pushed; partials saved to hints/
Loop until every sorry except EXTERNAL is closed.

Control files (in ROOT/pipeline/): STOP (exit), PAUSE (wait), COMPLETE.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError

HOME = Path.home()
ROOT = HOME / "hstar-separations-lean"
WORK = HOME / "hstar-sep-work"
PUSH = HOME / "vm-push"
PULLC = HOME / "vm-jules-pull"
CTRL = ROOT / "pipeline"
RUNS = ROOT / "pipeline_runs"
ATTENTION = HOME / "jules_needs_attention"
SEP_DIR = "HeadComplexity/Separations"

GH_REPO = "AlexeyMilovanov/vm"
GH_URL = f"https://github.com/{GH_REPO}"

AGY = str(HOME / ".local/bin/agy")
CLAUDE = str(HOME / ".npm-global/bin/claude")
CODEX = str(HOME / ".npm-global/bin/codex")
JULES = str(HOME / ".npm-global/bin/jules")
LAKE = str(HOME / ".elan/bin/lake")

GEMINI_MODEL = "gemini-3.1-pro-high"
CLAUDE_MODEL = "claude-opus-4-8"
CODEX_MODEL = "gpt-5.6-sol"

EXTERNAL = {"warren_sign_patterns_weak"}
MIN_QUEUE = 10
STAGE_TIMEOUT = 5400
BUILD_TIMEOUT = 2400
JULES_SESSION_BUDGET = 45 * 60   # sessions self-terminate in 15-25 min;
                                 # >40 min historically = drifting, not depth
JULES_PHASE_CAP = 2 * 3600
JULES_POLL = 60                  # fast poll so approve/nudge latency does
                                 # not eat into the 45-min budget
JULES_BATCH = 10
FORBIDDEN_RE = re.compile(
    r"^\s*(axiom|unsafe)\b|native_decide|\badmit\b|"
    r"set_option\s+(maxHeartbeats|maxRecDepth)", re.M)

BASE_URL = "https://jules.googleapis.com/v1alpha"


def log(msg: str):
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    line = f"[{stamp}] {msg}"
    print(line, flush=True)
    with open(CTRL / "pipeline.log", "a") as f:
        f.write(line + "\n")


def sh(cmd, cwd=None, timeout=600, check=False):
    r = subprocess.run(cmd, cwd=cwd, timeout=timeout, text=True,
                       capture_output=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"cmd failed ({r.returncode}): {cmd}\n"
                           f"{r.stdout[-2000:]}\n{r.stderr[-2000:]}")
    return r


def control_gate():
    while True:
        if (CTRL / "STOP").exists():
            log("STOP file present; exiting.")
            sys.exit(0)
        if (CTRL / "RESTART").exists():
            # soft code reload: exit cleanly at a stage boundary (nothing in
            # flight); the cron watchdog relaunches with the current code.
            # Completed stage work is audit-gated and committed in WORK, so
            # merge it into ROOT first — the relaunch resyncs WORK from ROOT
            # and no finished stage is lost.
            (CTRL / "RESTART").unlink(missing_ok=True)
            try:
                aok, _ = full_audit(WORK)
                if aok:
                    merge_work_to_root("soft-restart checkpoint")
                    log("RESTART: work merged to root")
                else:
                    log("RESTART: work audit not green, skipping merge")
            except Exception as exc:  # noqa: BLE001
                log(f"RESTART merge skipped: {exc}")
            log("RESTART: exiting at stage boundary for watchdog relaunch.")
            sys.exit(0)
        if (CTRL / "PAUSE").exists():
            time.sleep(60)
            continue
        return


# ---------------------------------------------------------------- census

def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def sorry_census(base: Path):
    """List (file, count) of CODE sorry occurrences in the Separations
    layer (doc-comments and line comments stripped first)."""
    out = {}
    for f in sorted((base / SEP_DIR).glob("*.lean")):
        n = len(re.findall(r"\bsorry\b", strip_comments(f.read_text())))
        if n:
            out[f.name] = n
    return out


def open_noncore_count(base: Path):
    total = sum(sorry_census(base).values())
    warren = base / SEP_DIR / "Warren.lean"
    ext = 0
    if warren.exists():
        ext = min(len(re.findall(r"\bsorry\b", warren.read_text())),
                  len(EXTERNAL))
    return total - ext


# ---------------------------------------------------------------- build/audit

def lake_build(cwd: Path, target=""):
    cmd = [LAKE, "-Kjobs=1", "build"] + ([target] if target else [])
    try:
        r = sh(cmd, cwd=cwd, timeout=BUILD_TIMEOUT)
    except subprocess.TimeoutExpired:
        return False, "build timeout"
    ok = r.returncode == 0 and "Build completed successfully" in r.stdout
    return ok, (r.stdout + r.stderr)[-6000:]


def smoke_build(cwd: Path):
    env = os.environ.copy()
    try:
        r = subprocess.run(
            [LAKE, "env", "lean", "scripts/smoke/FrozenStatements.lean"],
            cwd=cwd, timeout=900, text=True, capture_output=True, env=env)
    except subprocess.TimeoutExpired:
        return False, "smoke timeout"
    return r.returncode == 0, (r.stdout + r.stderr)[-4000:]


def forbidden_scan(base: Path):
    # comment-aware: a forbidden token in a doc-comment cost a full opus
    # stage on 2026-08-24 (REVERTED with green build+smoke)
    hits = []
    for f in sorted((base / SEP_DIR).glob("*.lean")):
        for m in FORBIDDEN_RE.finditer(strip_comments(f.read_text())):
            hits.append(f"{f.name}: {m.group(0).strip()}")
    return hits


def full_audit(cwd: Path):
    hits = forbidden_scan(cwd)
    if hits:
        return False, "forbidden constructs: " + "; ".join(hits[:10])
    ok, tail = lake_build(cwd)
    if not ok:
        return False, "build failed:\n" + tail
    ok, tail = smoke_build(cwd)
    if not ok:
        return False, "statement freeze violated (smoke failed):\n" + tail
    return True, "ok"


# ---------------------------------------------------------------- worktree

def sync_work_from_root():
    WORK.mkdir(exist_ok=True)
    sh(["rsync", "-a", "--delete",
        "--exclude", ".git", "--exclude", ".lake",
        "--exclude", "pipeline_runs", "--exclude", "pipeline",
        f"{ROOT}/", f"{WORK}/"], timeout=600, check=True)
    lake_dir = WORK / ".lake"
    lake_dir.mkdir(exist_ok=True)
    pkgs = lake_dir / "packages"
    if not pkgs.exists():
        pkgs.symlink_to(ROOT / ".lake" / "packages")
    build = lake_dir / "build"
    if not build.exists() and (ROOT / ".lake" / "build").exists():
        shutil.copytree(ROOT / ".lake" / "build", build, symlinks=True)
    if not (WORK / ".git").exists():
        sh(["git", "init", "-q"], cwd=WORK, check=True)
        sh(["git", "add", "-A"], cwd=WORK, timeout=300)
        sh(["git", "commit", "-qm", "baseline"], cwd=WORK, timeout=300)
    else:
        sh(["git", "add", "-A"], cwd=WORK, timeout=300)
        sh(["git", "commit", "-qm", "resync from root", "--allow-empty"],
           cwd=WORK, timeout=300)


def clean_scratch():
    """Agents keep leaving scratch files at the work-tree root; sweep the
    known patterns before committing a stage."""
    for pat in ["*.py", "scratch*", "tmp_*.lean", "fix_*.lean",
                "patch_*.lean", "test*.lean"]:
        for f in WORK.glob(pat):
            if f.is_file():
                f.unlink(missing_ok=True)


def work_commit(msg: str):
    clean_scratch()
    sh(["git", "add", "-A"], cwd=WORK, timeout=300)
    sh(["git", "commit", "-qm", msg, "--allow-empty"], cwd=WORK, timeout=300)


def work_reset_last_good():
    sh(["git", "reset", "--hard", "-q"], cwd=WORK, timeout=300)
    sh(["git", "clean", "-fdq", "-e", ".lake"], cwd=WORK, timeout=300)


def merge_work_to_root(msg: str):
    sh(["rsync", "-a", "--delete",
        f"{WORK}/{SEP_DIR}/", f"{ROOT}/{SEP_DIR}/"], timeout=300, check=True)
    for extra in ["PROOFS.md", "SEPARATIONS.md", "sorry_queue.json",
                  "PROGRESS.md"]:
        src = WORK / extra
        if src.exists():
            shutil.copy2(src, ROOT / extra)
    hints_src = WORK / "hints"
    if hints_src.exists():
        sh(["rsync", "-a", f"{hints_src}/", f"{ROOT}/hints/"], timeout=300)
    for bl in WORK.glob("BLOCKER_*.md"):
        shutil.copy2(bl, ROOT / bl.name)
    sh(["git", "add", "-A"], cwd=ROOT, timeout=300)
    sh(["git", "commit", "-qm", msg, "--allow-empty"], cwd=ROOT, timeout=300)


# ---------------------------------------------------------------- agents

def looks_quota(text: str):
    if len(text) > 2000:
        return False
    t = text.lower()
    return any(k in t for k in ["usage limit", "rate limit",
                                "resource_exhausted", "credit balance",
                                "quota"])


def run_agent(kind: str, prompt_file: Path, out_file: Path,
              timeout=STAGE_TIMEOUT):
    launcher = (f"You are working in the Lean repository {WORK}. Read the "
                f"file {prompt_file} fully and carry out the task it "
                f"describes. Work directly on the files in this repository.")
    if kind == "gemini":
        cmd = [AGY, "--mode", "accept-edits", "--dangerously-skip-permissions",
               "--model", GEMINI_MODEL, "--print-timeout", "85m",
               "--add-dir", str(WORK), "--print", launcher]
        stdin = None
    elif kind == "opus":
        cmd = [CLAUDE, "-p", "--model", CLAUDE_MODEL, "--effort", "max",
               "--dangerously-skip-permissions", "--no-session-persistence",
               "--add-dir", str(WORK)]
        stdin = launcher
    elif kind == "codex":
        cmd = [CODEX, "exec", "--ephemeral", "--skip-git-repo-check",
               "--sandbox", "workspace-write", "-C", str(WORK),
               "-m", CODEX_MODEL, "-c", 'model_reasoning_effort="xhigh"', "-"]
        stdin = launcher
    else:
        raise ValueError(kind)
    env = os.environ.copy()
    env["PATH"] = f"{HOME}/.local/bin:{HOME}/.npm-global/bin:" \
                  f"{HOME}/.elan/bin:" + env.get("PATH", "")
    env.update({"NO_COLOR": "1", "TERM": "dumb"})
    try:
        r = subprocess.run(cmd, cwd=WORK, input=stdin, text=True,
                           capture_output=True, timeout=timeout, env=env)
        text = (r.stdout or "") + ("\n--stderr--\n" + r.stderr
                                   if r.stderr else "")
        out_file.write_text(text)
        if r.returncode != 0 or looks_quota(r.stdout or ""):
            return False
        return True
    except subprocess.TimeoutExpired:
        out_file.write_text("STAGE TIMEOUT")
        return False


def run_stage(kind: str, role_prompt: str, iter_dir: Path, name: str):
    control_gate()
    pf = iter_dir / f"{name}.prompt.md"
    pf.write_text(role_prompt)
    out = iter_dir / f"{name}.out.md"
    log(f"stage {name} ({kind}) starting")
    ok = run_agent(kind, pf, out)
    if not ok and kind in ("opus", "codex"):
        log(f"stage {name}: {kind} failed/quota -> gemini fallback")
        ok = run_agent("gemini", pf, iter_dir / f"{name}.fallback.out.md")
    # build check + one repair
    bok, tail = lake_build(WORK)
    if not bok:
        log(f"stage {name}: build broken, gemini repair")
        rp = iter_dir / f"{name}.repair.prompt.md"
        rp.write_text(REPAIR_PROMPT + "\n\nBuild log tail:\n```\n"
                      + tail + "\n```\n")
        run_agent("gemini", rp, iter_dir / f"{name}.repair.out.md",
                  timeout=3600)
        bok, tail = lake_build(WORK)
    hits = forbidden_scan(WORK)
    sok, stail = smoke_build(WORK) if bok else (False, "skipped")
    if bok and sok and not hits:
        work_commit(f"stage {name}")
        log(f"stage {name}: committed")
        return True
    log(f"stage {name}: REVERTED (build={bok} smoke={sok} "
        f"forbidden={len(hits)})")
    work_reset_last_good()
    return False


# ---------------------------------------------------------------- prompts

COMMON = f"""## Project context (read these files first, in this order)
1. `SEPARATIONS.md` — the layer map, statement freeze, attack order.
2. `PROOFS.md` — the audited detailed proof for EVERY sorry leaf
   (P-numbered items). Your Lean work must follow these proofs.
3. `sorry_queue.json` — the current queue state (create it if missing, from
   the SEPARATIONS.md status table).
4. `PROGRESS.md` — the running log (create if missing; append, never rewrite).

## Hard rules
- FORBIDDEN anywhere: `axiom`, `admit`, `native_decide`, `unsafe`,
  `set_option maxHeartbeats/maxRecDepth`. Honest `sorry` leaves are allowed.
- STATEMENT FREEZE: the theorem statements re-stated in
  `scripts/smoke/FrozenStatements.lean` must remain provable verbatim from
  the layer (do not rename/weaken/re-hypothesize them, do not edit the smoke
  file). Helper lemmas are NOT frozen: you may fix a wrong helper statement,
  but then update the matching item in PROOFS.md and log it in PROGRESS.md.
  If a FROZEN statement seems false, do NOT touch it — write
  `BLOCKER_<name>.md` with the argument instead.
- EXTERNAL (never attempt, never queue as jules_ready):
  `warren_sign_patterns`.
- Always finish with a green `lake build` (run it yourself; fix what you
  broke). Also run `lake env lean scripts/smoke/FrozenStatements.lean`.
- Maintain `sorry_queue.json`: a JSON object
  {{"entries": [{{"name": <decl>, "file": <path>, "status":
  "jules_ready"|"hard"|"external", "pref": <PROOFS.md item>, "note": <str>}}]}}
  listing EVERY declaration that currently contains `sorry`.
  `jules_ready` means: a self-contained statement a competent Lean/mathlib
  user can prove in about 30-40 minutes by following the referenced
  PROOFS.md item (no new decomposition needed, no deep external theory).
- Append to `PROGRESS.md`: what you proved, decomposed, fixed, or found.
"""

ROLE_AUDIT_PROVE = COMMON + """
## Your task (auditor + prover)
1. AUDIT: go through every declaration that contains `sorry` in
   `HeadComplexity/Separations/`. For each, check the statement against its
   PROOFS.md item: right hypotheses, right types, actually provable as
   stated. Fix wrong NON-frozen statements (updating PROOFS.md + PROGRESS.md).
2. MANDATORY DECOMPOSITION: pick the single HARDEST open sorry in your
   judgment (justify the choice in one PROGRESS.md line; if an earlier stage
   of this iteration already decomposed a leaf, pick the hardest one not yet
   touched this iteration) and split it into 2-4 named helper lemmas keyed
   to the PROOFS.md steps.  Granularity target: each helper is a
   self-contained statement a competent Lean/mathlib prover closes in about
   20-30 minutes.  No vacuous splits: every helper must be a substantive
   step of the actual proof, and the parent gets an assembly recipe in its
   docstring/queue note.  This duty is IN ADDITION to items 1 and 3.
3. PROVE: fully prove the easiest open sorries (start with the ones the
   queue marks jules_ready or SEPARATIONS.md marks easy). Quality over
   quantity — every proof must compile.  Decompose further hard sorries as
   time permits (same granularity rules).
4. Update sorry_queue.json + PROGRESS.md; leave the build green.
"""

ROLE_DO = COMMON + """
## Your task (prover)
Prove open sorries and/or decompose hard ones into jules_ready helper
lemmas, following PROOFS.md faithfully. Pick targets by the SEPARATIONS.md
attack order and the queue. Do not audit broadly — produce proofs. Keep the
build green; update sorry_queue.json + PROGRESS.md.
"""

ROLE_CHECK = COMMON + """
## Your task (checker)
Review what the previous agent just did: run `git log --oneline -3` and
`git diff HEAD~1` in this repository. Verify each change:
- proofs are honest (no vacuous statements, no hypothesis smuggling, no
  weakened conclusions, no dead helper lemmas that prove nothing relevant);
- new helper lemma statements really capture the PROOFS.md step they cite
  and suffice for the parent;
- sorry_queue.json matches reality (every sorried decl listed; jules_ready
  labels justified).
Fix every problem you find directly. Keep the build green; log findings in
PROGRESS.md.
"""

ROLE_FINAL = COMMON + f"""
## Your task (final gatekeeper of this iteration)
1. Re-audit the layer end-to-end: build green, smoke green, no forbidden
   constructs, every sorried decl present in sorry_queue.json with an honest
   status, PROGRESS.md up to date.
2. The pipeline will hand every `jules_ready` leaf to an autonomous
   45-minute Jules session. Make the queue as large and as clean as you
   can; if fewer
   than {MIN_QUEUE} leaves are jules_ready and some `hard` entries are close,
   decompose them now to cross the threshold.
3. For each jules_ready entry double-check: statement compiles, is
   self-contained, has a precise PROOFS.md reference in `pref`, and a
   one-line `note` telling the prover where to start.
"""

REPAIR_PROMPT = COMMON + """
## Your task (build repair)
The build is broken after the previous stage. Fix compilation errors ONLY —
smallest possible change, no new mathematics, never touch frozen statements.
If a new lemma from the previous stage is unfixable, comment it out... no —
instead replace its proof with `sorry` (honest leaf) rather than deleting
the statement, unless the statement itself is malformed (then remove it and
note this in PROGRESS.md).
"""


def jules_prompt(entry, base_sha):
    hard_note = ""
    if entry.get("status") == "hard":
        hard_note = """
NOTE: this target is classified HARD — a complete proof within your budget
is not expected. Success criteria, in order of preference: (a) full proof;
(b) a real reduction: fully proved new helper lemmas implementing the first
steps of the PROOFS.md item, with the target proved from the helpers modulo
remaining helper `sorry`s (this is allowed for a HARD target: new helper
lemmas may carry `sorry` if they are honest, clearly-stated sub-steps);
(c) fully proved standalone helper lemmas. Never fake progress.
"""
    return hard_note + f"""Prove exactly one Lean 4 lemma in the repository {GH_REPO}.

Base commit: {base_sha} (branch main). First run `git rev-parse HEAD`; if it
differs from the base commit, reply exactly BASE_COMMIT_MISMATCH and stop.

Target declaration: `{entry['name']}` in `{entry['file']}` — it currently
ends in `sorry`.

The repository contains an audited detailed proof plan: open `PROOFS.md`
and follow item {entry.get('pref', '(search by name)')} for this exact
lemma. Context map: `SEPARATIONS.md`. Hint from the queue:
{entry.get('note', '(none)')}

If `hints/{entry['name']}.diff` exists it is a previous partial attempt —
read it critically and reuse what is sound.

Rules:
1. Remove ONLY the `sorry` of the target declaration (plus you may add NEW
   private helper lemmas placed immediately above it). Do not modify any
   other declaration, statement, hypothesis, file header, toolchain, or
   lakefile. In particular do NOT touch or re-prove any OTHER declaration
   that contains `sorry` — other autonomous sessions own those in parallel,
   and overlapping edits get both patches rejected. Never edit
   `scripts/smoke/FrozenStatements.lean`.
2. Forbidden: `sorry` (in your final version of the target), `admit`,
   `axiom`, `native_decide`, `unsafe`, `set_option maxHeartbeats`,
   `set_option maxRecDepth`, linter suppressions.
3. Verify: `lake exe cache get` (first time), then `lake build` must succeed
   with the target sorry-free (warnings about OTHER sorries in the layer are
   expected and fine), and
   `lake env lean scripts/smoke/FrozenStatements.lean` must succeed.
4. Budget: about 40 minutes. If a complete proof is out of reach, make
   honest partial progress: prove some of the needed helper steps fully
   (new lemmas, no sorries in THEM), keep the target as `sorry`, and say
   clearly in your final report what remains.
5. If you become convinced the target statement is FALSE, do not weaken it;
   write a file `BLOCKER_{entry['name']}.md` with the counterexample
   argument and stop.
Final report: list changed files and state whether the target is sorry-free.
"""


JULES_NUDGE = ("Proceed with your best judgment; you do not need my "
               "approval. Remember: do not change any existing statement; "
               "follow PROOFS.md; if the full proof is out of reach in your "
               "2-hour budget, commit fully-proved helper lemmas and leave "
               "the target as sorry with a clear report. If you believe the "
               "statement is false, write BLOCKER_<name>.md instead.")


# ---------------------------------------------------------------- queue

def load_queue(base: Path):
    qf = base / "sorry_queue.json"
    if not qf.exists():
        return []
    try:
        data = json.loads(qf.read_text())
        return data.get("entries", [])
    except json.JSONDecodeError:
        return []


def validated_entries(base: Path, statuses=("jules_ready",)):
    out = []
    for e in load_queue(base):
        if e.get("status") not in statuses:
            continue
        name, file = e.get("name", ""), e.get("file", "")
        if name in EXTERNAL or not name or not file:
            continue
        fp = base / file
        if not fp.exists():
            continue
        text = fp.read_text()
        if name in text and "sorry" in text:
            out.append(e)
    return out


# ---------------------------------------------------------------- github

def ensure_clones():
    if not PUSH.exists():
        sh(["git", "clone", "-q", GH_URL, str(PUSH)], timeout=600, check=True)
    if not PULLC.exists():
        sh(["git", "clone", "-q", GH_URL, str(PULLC)], timeout=600,
           check=True)


def push_root_to_github(msg: str):
    ensure_clones()
    sh(["git", "-C", str(PUSH), "fetch", "-q", "origin"], timeout=300)
    sh(["git", "-C", str(PUSH), "checkout", "-qf", "main"], timeout=120)
    sh(["git", "-C", str(PUSH), "reset", "--hard", "-q", "origin/main"],
       timeout=120)
    sh(["rsync", "-a", "--delete",
        "--exclude", ".git", "--exclude", ".lake",
        "--exclude", "pipeline_runs", "--exclude", "pipeline",
        "--exclude", "build.log", "--exclude", "audit",
        f"{ROOT}/", f"{PUSH}/"], timeout=600, check=True)
    # keep audit sources (referenced by PROOFS.md) but drop bulky reports
    (PUSH / "audit" / "sources").mkdir(parents=True, exist_ok=True)
    sh(["rsync", "-a", f"{ROOT}/audit/sources/", f"{PUSH}/audit/sources/"],
       timeout=120)
    sh(["git", "-C", str(PUSH), "add", "-A"], timeout=300)
    r = sh(["git", "-C", str(PUSH), "commit", "-qm", msg], timeout=120)
    if r.returncode != 0 and "nothing to commit" not in (r.stdout + r.stderr):
        log(f"push commit warning: {r.stdout[-200:]} {r.stderr[-200:]}")
    p = sh(["git", "-C", str(PUSH), "push", "-q", "origin", "main"],
           timeout=600)
    if p.returncode != 0:
        raise RuntimeError("git push failed: " + p.stderr[-1000:])
    sha = sh(["git", "-C", str(PUSH), "rev-parse", "HEAD"],
             timeout=60).stdout.strip()
    log(f"pushed to {GH_REPO} main = {sha}")
    return sha


# ---------------------------------------------------------------- jules api

def api_key():
    k = os.environ.get("JULES_WEB_API_KEY")
    if not k:
        k = (HOME / ".jules" / "web_api_key").read_text().strip()
    return k


def api(method, path, body=None):
    url = BASE_URL + path
    data = json.dumps(body).encode() if body is not None else None
    headers = {"accept": "application/json", "x-goog-api-key": api_key()}
    if data is not None:
        headers["content-type"] = "application/json"
    req = Request(url, data=data, method=method, headers=headers)
    for attempt in range(3):
        try:
            with urlopen(req, timeout=60) as resp:
                return resp.status, json.loads(
                    resp.read().decode("utf-8", "replace") or "{}")
        except HTTPError as exc:
            try:
                return exc.code, json.loads(
                    exc.read().decode("utf-8", "replace") or "{}")
            except json.JSONDecodeError:
                return exc.code, {}
        except (URLError, json.JSONDecodeError, TimeoutError):
            if attempt == 2:
                return 599, {}
            time.sleep(3)
    return 599, {}


def fetch_activities(sid):
    acts, token, pages = [], None, 0
    while pages < 10:
        pages += 1
        path = f"/sessions/{sid}/activities?pageSize=100"
        if token:
            path += f"&pageToken={token}"
        st, body = api("GET", path)
        if st != 200 or not isinstance(body, dict):
            return None
        acts.extend(body.get("activities", []))
        token = body.get("nextPageToken")
        if not token:
            break
    acts.sort(key=lambda a: a.get("createTime", ""))
    return acts


def latest_trigger(sid, state):
    """Newest planGenerated/agentMessaged not yet answered by the user side.
    Mirrors find_trigger_activity of the KolmogorovMathlib2 responder: walk
    newest-first; a userMessaged/planApproved seen first means we already
    responded and the state is just lagging."""
    acts = fetch_activities(sid)
    if acts is None:
        return None
    for a in reversed(acts):
        if "userMessaged" in a or "planApproved" in a:
            return None
        if state == "AWAITING_PLAN_APPROVAL" and "planGenerated" in a:
            return a.get("name") or a.get("createTime") or "plan"
        if state == "AWAITING_USER_FEEDBACK" and "agentMessaged" in a:
            return a.get("name") or a.get("createTime") or "msg"
    return None


def escalate(campaign, task_id, session_id, reason):
    ATTENTION.mkdir(exist_ok=True)
    sid = session_id.replace("sessions/", "")
    payload = {"campaign": campaign, "task_id": task_id,
               "session_id": sid,
               "session_url": f"https://jules.google.com/session/{sid}",
               "reason": reason,
               "exported_at": datetime.now(timezone.utc).isoformat()}
    (ATTENTION / f"{campaign}__{task_id}.json").write_text(
        json.dumps(payload, indent=2))


def jules_submit(entry, base_sha, logdir: Path):
    prompt = jules_prompt(entry, base_sha)
    for attempt in range(6):
        try:
            r = subprocess.run([JULES, "remote", "new", "--repo", GH_REPO,
                                "--session", prompt],
                               text=True, capture_output=True, timeout=180)
        except (OSError, subprocess.TimeoutExpired) as exc:
            (logdir / f"{entry['name']}.submit.log").write_text(str(exc))
            time.sleep(60)
            continue
        out = (r.stdout or "") + (r.stderr or "")
        (logdir / f"{entry['name']}.submit.log").write_text(out)
        ids = re.findall(r"(?<!\d)(\d{10,20})(?!\d)", out)
        if r.returncode == 0 and ids:
            return ids[0]
        if "FAILED_PRECONDITION" in out or "Precondition" in out:
            log(f"jules capacity for {entry['name']}; wait 10m "
                f"(attempt {attempt + 1}/6)")
            time.sleep(600)
            continue
        return None
    return None


def jules_pull(session_id):
    sh(["git", "-C", str(PULLC), "fetch", "-q", "origin"], timeout=300)
    sh(["git", "-C", str(PULLC), "checkout", "-qf", "main"], timeout=120)
    sh(["git", "-C", str(PULLC), "reset", "--hard", "-q", "origin/main"],
       timeout=120)
    sh(["git", "-C", str(PULLC), "clean", "-fdq"], timeout=120)
    try:
        r = subprocess.run([JULES, "remote", "pull", "--session", session_id],
                           cwd=PULLC, capture_output=True, text=True,
                           timeout=300)
    except subprocess.TimeoutExpired:
        return ""
    patch = (r.stdout or "").strip()
    if patch.lstrip().startswith("diff --git") and len(patch) > 50:
        return patch + "\n"
    # fallback: the pull may have materialized changes in the worktree
    d = sh(["git", "-C", str(PULLC), "diff"], timeout=120).stdout
    return d if len(d.strip()) > 50 else ""


ALLOWED_PATCH_RE = re.compile(
    r"^(HeadComplexity/|PROOFS\.md$|PROGRESS\.md$|sorry_queue\.json$|"
    r"BLOCKER_[A-Za-z0-9_']+\.md$|hints/)")


def patch_paths(patch: str):
    return re.findall(r"^diff --git a/(\S+) b/\S+", patch, re.M)


def structural_ok(patch: str):
    paths = patch_paths(patch)
    if not paths:
        return False, "empty patch"
    bad = [p for p in paths if not ALLOWED_PATCH_RE.match(p)]
    if bad:
        return False, f"disallowed paths: {bad[:5]}"
    added = "\n".join(l[1:] for l in patch.splitlines()
                      if l.startswith("+") and not l.startswith("+++"))
    m = FORBIDDEN_RE.search(added)
    if m:
        return False, f"forbidden construct in patch: {m.group(0).strip()}"
    return True, "ok"


def semantic_review(entry, patch_file: Path, iter_dir: Path):
    pf = iter_dir / f"review_{entry['name']}.prompt.md"
    pf.write_text(f"""You are reviewing a patch produced by an autonomous
prover for the Lean repository {WORK}. The patch (already applied to the
repository you are in) targets the declaration `{entry['name']}` in
`{entry['file']}`; the intended proof is PROOFS.md item
{entry.get('pref', '?')}. The build and the frozen-statement check already
passed. Your job is SEMANTIC review only:
- Read the new/changed proof code (`git diff HEAD` shows the patch, also
  saved at {patch_file}).
- Check the proof is honest: no vacuous or irrelevant helper lemmas, no
  statement drift on the target or its helpers, the mathematics matches the
  PROOFS.md item (or is a legitimate alternative proof).
Print exactly one line first: VERDICT: ACCEPT or VERDICT: REJECT, then a
short justification. Do not modify any files.""")
    out = iter_dir / f"review_{entry['name']}.out.md"
    run_agent("gemini", pf, out, timeout=2400)
    text = out.read_text() if out.exists() else ""
    return "VERDICT: ACCEPT" in text, text[-1500:]


def target_closed(base: Path, entry):
    fp = base / entry["file"]
    if not fp.exists():
        return False
    text = fp.read_text()
    # Match the declaration name itself, not a private helper whose name merely
    # has the target as a prefix (for example `target_priv`).
    decl = re.search(
        r"(?m)^(?:noncomputable\s+)?"
        r"(?:theorem|lemma|def|instance|abbrev|structure)\s+"
        + re.escape(entry["name"])
        + r"(?=\s|\(|:)",
        text)
    if decl is None:
        return False
    idx = decl.start()
    nxt = re.search(
        r"\n(?:noncomputable\s+)?"
        r"(?:theorem|lemma|def|instance|abbrev|structure|end)\s",
        text[decl.end():])
    stop = decl.end() + (nxt.start() if nxt else len(text))
    block = text[idx:stop]
    return "sorry" not in block


# ---------------------------------------------------------------- jules phase

def jules_phase(ready, base_sha, iter_dir: Path):
    campaign = f"hstar_{iter_dir.parent.name}_{iter_dir.name}"
    jdir = iter_dir / "jules"
    jdir.mkdir(exist_ok=True)
    sessions = {}
    for i in range(0, len(ready), JULES_BATCH):
        for entry in ready[i:i + JULES_BATCH]:
            control_gate()
            sid = jules_submit(entry, base_sha, jdir)
            if sid:
                sessions[sid] = {"entry": entry, "t0": time.time(),
                                 "nudged": 0, "state": "submitted",
                                 "reviewed": False, "acted": set()}
                log(f"jules submitted {entry['name']} session={sid}")
            else:
                log(f"jules submit FAILED for {entry['name']}")
            time.sleep(5)
    (jdir / "sessions.json").write_text(json.dumps(
        {s: v["entry"]["name"] for s, v in sessions.items()}, indent=2))

    merged, partial = [], []
    phase_t0 = time.time()
    sync_work_from_root()  # WORK becomes the review area

    def review(sid, info, reason):
        entry = info["entry"]
        info["reviewed"] = True
        patch = jules_pull(sid)
        pfile = jdir / f"{entry['name']}.patch"
        if not patch:
            log(f"review {entry['name']}: no patch ({reason})")
            return
        pfile.write_text(patch)
        ok, why = structural_ok(patch)
        if not ok:
            log(f"review {entry['name']}: structural reject: {why}")
            (ROOT / "hints").mkdir(exist_ok=True)
            shutil.copy2(pfile, ROOT / "hints" / f"{entry['name']}.diff")
            partial.append(entry["name"])
            return
        # 3-way first: neighbours' accepted patches shift context in the
        # same files, and plain apply threw away complete proofs in wave 1
        ap = sh(["git", "apply", "--3way", "--whitespace=nowarn",
                 str(pfile)], cwd=WORK, timeout=120)
        if ap.returncode != 0:
            sh(["git", "reset", "--hard", "-q"], cwd=WORK, timeout=120)
            sh(["git", "clean", "-fdq", "-e", ".lake"], cwd=WORK,
               timeout=120)
            ap = sh(["git", "apply", "--whitespace=nowarn", str(pfile)],
                    cwd=WORK, timeout=120)
        if ap.returncode != 0:
            log(f"review {entry['name']}: patch does not apply (3way+plain)")
            shutil.copy2(pfile, ROOT / "hints" / f"{entry['name']}.diff")
            partial.append(entry["name"])
            return
        closed = target_closed(WORK, entry)
        if closed:
            aok, why = full_audit(WORK)
        else:
            aok = False
            why = "target remains open"
        acc = False
        if aok and closed:
            acc, verdict = semantic_review(entry, pfile, jdir)
            log(f"review {entry['name']}: audit=ok closed=yes "
                f"semantic={'ACCEPT' if acc else 'REJECT'}")
        else:
            log(f"review {entry['name']}: audit={aok} closed={closed}")
        if acc:
            work_commit(f"jules: close {entry['name']}")
            merged.append(entry["name"])
        else:
            work_reset_last_good()
            (ROOT / "hints").mkdir(exist_ok=True)
            shutil.copy2(pfile, ROOT / "hints" / f"{entry['name']}.diff")
            partial.append(entry["name"])

    while sessions and time.time() - phase_t0 < JULES_PHASE_CAP:
        control_gate()
        pending = False
        for sid, info in list(sessions.items()):
            if info["reviewed"]:
                continue
            age = time.time() - info["t0"]
            st, body = api("GET", f"/sessions/{sid}")
            state = (body or {}).get("state", "UNKNOWN")
            info["state"] = state
            if state == "COMPLETED":
                review(sid, info, "completed")
            elif state == "FAILED":
                # the platform can flag FAILED right after the agent finished
                # (seen 2026-08-24: complete proof delivered, then
                # sessionFailed 2s later) — always pull and review the diff
                log(f"jules {info['entry']['name']}: FAILED — pulling diff "
                    f"anyway")
                review(sid, info, "failed")
            elif age > JULES_SESSION_BUDGET:
                log(f"jules {info['entry']['name']}: 2h budget over, "
                    f"pulling partial (state={state})")
                review(sid, info, "budget")
            elif state == "AWAITING_PLAN_APPROVAL":
                # act only on a fresh unanswered planGenerated activity
                # (state lags after approvePlan; plans can have revisions,
                # each needing its own approval)
                trig = latest_trigger(sid, state)
                if trig and trig not in info["acted"]:
                    st2, _ = api("POST", f"/sessions/{sid}:approvePlan",
                                 body={})
                    info["acted"].add(trig)
                    log(f"jules {info['entry']['name']}: plan approved "
                        f"(http {st2})")
                pending = True
            elif state == "AWAITING_USER_FEEDBACK":
                trig = latest_trigger(sid, state)
                if trig and trig not in info["acted"]:
                    if info["nudged"] < 2:
                        api("POST", f"/sessions/{sid}:sendMessage",
                            body={"prompt": JULES_NUDGE})
                        info["nudged"] += 1
                        info["acted"].add(trig)
                        log(f"jules {info['entry']['name']}: nudged "
                            f"({info['nudged']}/2)")
                    else:
                        escalate(campaign, info["entry"]["name"], sid,
                                 "third AWAITING_USER_FEEDBACK question "
                                 "after 2 nudges")
                        info["reviewed"] = True
                        log(f"jules {info['entry']['name']}: escalated to "
                            f"jules_needs_attention")
                pending = True
            else:
                pending = True
        if not pending and all(i["reviewed"] for i in sessions.values()):
            break
        time.sleep(JULES_POLL)

    for sid, info in sessions.items():
        if not info["reviewed"]:
            review(sid, info, "phase timeout")

    # publish accepted work
    if merged:
        merge_work_to_root(f"jules phase {iter_dir.name}: merged "
                           + ", ".join(merged))
        push_root_to_github(f"jules merges: {', '.join(merged)}")
    prog = ROOT / "PROGRESS.md"
    with open(prog, "a") as f:
        f.write(f"\n## Jules phase {iter_dir.name} "
                f"({datetime.now(timezone.utc).date()})\n"
                f"- merged: {merged or 'none'}\n"
                f"- partial (hints saved): {partial or 'none'}\n")
    sh(["git", "-C", str(ROOT), "add", "-A"], timeout=120)
    sh(["git", "-C", str(ROOT), "commit", "-qm",
        f"jules phase {iter_dir.name} bookkeeping", "--allow-empty"],
       timeout=120)
    log(f"jules phase done: merged={merged} partial={partial}")


# ---------------------------------------------------------------- main loop

STAGES = [("opus", ROLE_AUDIT_PROVE, "s1_opus_audit"),
          ("gemini", ROLE_DO, "s2_gemini_do"),
          ("gemini", ROLE_CHECK, "s3_gemini_check"),
          ("codex", ROLE_AUDIT_PROVE, "s4_codex_audit"),
          ("gemini", ROLE_DO, "s5_gemini_do"),
          ("gemini", ROLE_CHECK, "s6_gemini_check"),
          ("opus", ROLE_FINAL, "s7_opus_final")]


def one_iteration(run_dir: Path, n: int):
    iter_dir = run_dir / f"iter_{n:03d}"
    iter_dir.mkdir(parents=True, exist_ok=True)
    open_n = open_noncore_count(ROOT)
    log(f"=== iteration {n}: {open_n} non-external sorries open ===")
    if open_n <= 0:
        (CTRL / "COMPLETE").write_text("all non-external sorries closed\n")
        log("COMPLETE: all non-external sorries closed")
        sys.exit(0)
    sync_work_from_root()
    for kind, role, name in STAGES:
        run_stage(kind, role, iter_dir, name)
    aok, why = full_audit(WORK)
    if not aok:
        log(f"iteration {n}: final audit failed ({why[:300]}); "
            f"reverting to last good stage state")
        work_reset_last_good()
        aok2, _ = full_audit(WORK)
        if not aok2:
            log(f"iteration {n}: work tree unusable, skipping merge")
            return
    merge_work_to_root(f"pipeline iteration {n}")
    ready = validated_entries(ROOT, ("jules_ready",))
    hard = validated_entries(ROOT, ("hard",))
    log(f"iteration {n}: {len(ready)} jules-ready + {len(hard)} hard "
        f"validated leaves")
    if len(ready) + len(hard) < MIN_QUEUE:
        log(f"iteration {n}: below threshold {MIN_QUEUE} total leaves, "
            f"next local iteration")
        return
    sha = push_root_to_github(
        f"pipeline iteration {n}: {len(ready)} jules-ready + "
        f"{len(hard)} hard leaves")
    # everything non-external goes to Jules: easy leaves first (they win
    # capacity slots), hard leaves after — partial progress expected there
    jules_phase(ready + hard, sha, iter_dir)


def main():
    CTRL.mkdir(exist_ok=True)
    import fcntl
    lock_fd = os.open(CTRL / "driver.lock", os.O_RDWR | os.O_CREAT, 0o644)
    try:
        fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("another driver instance is running; exiting")
        sys.exit(0)
    (ROOT / "hints").mkdir(exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_dir = RUNS / stamp
    run_dir.mkdir(parents=True, exist_ok=True)
    log(f"pipeline started, run dir {run_dir}")
    start = 1
    if len(sys.argv) > 2 and sys.argv[1] == "--start-iteration":
        start = int(sys.argv[2])
    n = start
    while n <= 500:
        control_gate()
        try:
            one_iteration(run_dir, n)
        except Exception as exc:  # noqa: BLE001 — keep the loop alive
            log(f"iteration {n} crashed: {type(exc).__name__}: {exc}")
            time.sleep(120)
        n += 1


if __name__ == "__main__":
    main()
