#!/usr/bin/env python3
"""Load a case as the 9-bit Boolean truth table expected by the common solvers."""
import json, sys
from pathlib import Path
import numpy as np

case = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
data = json.loads((case / "input.json").read_text())
X = ((np.arange(512)[:, None] >> np.arange(9)) & 1).astype(float)
f = ((np.asarray(data["truth_table_pm"], dtype=float) + 1.0) / 2.0)
assert np.all((f == 0) | (f == 1))
print(data["case_id"], "n=9", "ones=", int(f.sum()), "of", len(f))
