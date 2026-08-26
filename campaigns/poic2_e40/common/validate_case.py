#!/usr/bin/env python3
"""Validate an immutable case input and the basic result envelope."""
import hashlib, json, sys
from pathlib import Path

case = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
data = json.loads((case / "input.json").read_text())
claimed = data.pop("input_sha256")
raw = json.dumps(data, sort_keys=True, separators=(",", ":")).encode()
assert hashlib.sha256(raw).hexdigest() == claimed
assert data["schema"] == "poic2-e40-case-v1"
assert data["grid"] == [6, 5] and data["block_sizes"] == [5, 4]
table = data["weight_table_pm"]
assert len(table) == 6 and all(len(row) == 5 for row in table)
assert all(x in (-1, 1) for row in table for x in row)
truth = data["truth_table_pm"]
assert len(truth) == 512 and all(x in (-1, 1) for x in truth)
for mask, value in enumerate(truth):
    r = sum((mask >> i) & 1 for i in range(5))
    s = sum((mask >> i) & 1 for i in range(5, 9))
    assert value == table[r][s]
result = case / "result.json"
if result.exists():
    out = json.loads(result.read_text())
    assert out["case_id"] == data["case_id"]
    assert out["input_sha256"] == claimed
    assert out["status"] in {
        "UNRESOLVED", "POIC2_LE_3_NUMERICAL", "POIC2_EQ_3_EXACT",
        "H3_NUMERICAL_FOUND", "H3_EXACT_FOUND", "INVALID_TARGET"
    }
print("PASS", data["case_id"], claimed)
