import sys, subprocess, os
from pathlib import Path
sys.path.insert(0, str(Path.home() / "hstar-separations-lean" / "scripts"))
from sorry_pipeline import (ROOT, CTRL, validated_entries, push_root_to_github,
                            jules_phase, log)
ready = validated_entries(ROOT, ("jules_ready",))
hard = validated_entries(ROOT, ("hard",))
log(f"manual wave: {len(ready)} ready + {len(hard)} hard")
sha = push_root_to_github(f"manual decomposition wave: {len(ready)}+{len(hard)} leaves")
iter_dir = ROOT / "pipeline_runs" / "manual_wave_01" / "iter_001"
iter_dir.mkdir(parents=True, exist_ok=True)
try:
    jules_phase(ready + hard, sha, iter_dir)
finally:
    (CTRL / "PAUSE").unlink(missing_ok=True)
    subprocess.Popen(["nohup", "setsid", "nice", "-n", "10", "python3",
                      "scripts/sorry_pipeline.py"], cwd=ROOT,
                     stdout=open(CTRL / "driver.nohup.log", "a"),
                     stderr=subprocess.STDOUT,
                     stdin=subprocess.DEVNULL)
    log("manual wave finished; PAUSE cleared; driver relaunched")
