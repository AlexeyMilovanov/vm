#!/usr/bin/env python3
from __future__ import annotations

import copy
import importlib.util
import itertools
import json
import os
from pathlib import Path
import random
import struct
import subprocess
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
TABLE = Path(os.environ.get(
    "N5_CERTIFICATE_TABLE",
    "/home/lesha/n5-certificate-table-build/candidate-v2/merged-complete-v1",
))
SPEC = importlib.util.spec_from_file_location("submission_verifier", HERE / "verify_submission.py")
assert SPEC is not None and SPEC.loader is not None
VERIFIER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFIER)


class SubmissionVerifierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        manifest = json.loads((TABLE / "manifest.json").read_text(encoding="ascii"))
        cls.constant = json.loads(
            (TABLE / manifest["shards"][0]["path"]).read_text(encoding="ascii").splitlines()[0]
        )
        with (TABLE / manifest["shards"][1]["path"]).open("r", encoding="ascii") as handle:
            cls.nonconstant = json.loads(next(handle))

    def test_burnside(self) -> None:
        self.assertEqual(
            VERIFIER.burnside_orbit_count(),
            {"group_size": 480, "fixed_sum": 4_483_480_320, "orbits": 9_340_584},
        )

    def test_two_real_rows(self) -> None:
        self.assertEqual(VERIFIER.verify_row(self.constant)["truth_table"], 0)
        self.assertGreater(
            VERIFIER.verify_row(self.nonconstant)["minimum_abs_score"][0], 0
        )

    def test_bad_upper_is_rejected(self) -> None:
        row = copy.deepcopy(self.nonconstant)
        row["upper"]["theta"] = [[0, 1] for _ in row["upper"]["theta"]]
        with self.assertRaises(VERIFIER.VerificationError):
            VERIFIER.verify_row(row)

    def test_bad_lower_is_rejected(self) -> None:
        row = copy.deepcopy(self.nonconstant)
        if row["lower"]["weights"]:
            row["lower"]["weights"][0][1] += 1
            with self.assertRaises(VERIFIER.VerificationError):
                VERIFIER.verify_row(row)

    def test_coverage_accelerator_positive_and_negative(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            binary = root / "coverage_fast"
            subprocess.run(
                [
                    "cc", "-O3", "-std=c11", "-Wall", "-Wextra", "-Werror",
                    "-fopenmp", str(HERE / "coverage_fast.c"), "-o", str(binary),
                ],
                check=True,
            )
            good = root / "good.u32le"
            good.write_bytes(struct.pack("<II", 0, 1))
            accepted = subprocess.run(
                [str(binary), str(good), "2", "2"],
                text=True,
                capture_output=True,
            )
            self.assertEqual(accepted.returncode, 0, accepted.stderr)
            self.assertTrue(json.loads(accepted.stdout)["ok"])

            bad = root / "bad.u32le"
            # Code 4 is the coordinate-permuted image of the smaller code 2.
            bad.write_bytes(struct.pack("<I", 4))
            rejected = subprocess.run(
                [str(binary), str(bad), "1", "2"],
                text=True,
                capture_output=True,
            )
            self.assertEqual(rejected.returncode, 1, rejected.stderr)
            self.assertFalse(json.loads(rejected.stdout)["ok"])

            def canonical(code: int) -> int:
                result = code
                for permutation in itertools.permutations(range(5)):
                    for input_flip in (0, 1):
                        transformed = 0
                        for vertex in range(32):
                            source = 0
                            for coordinate in range(5):
                                bit = ((vertex >> permutation[coordinate]) & 1) ^ input_flip
                                source |= bit << coordinate
                            if (code >> source) & 1:
                                transformed |= 1 << vertex
                        result = min(result, transformed, transformed ^ 0xFFFFFFFF)
                return result

            generator = random.Random(20260830)
            raw_codes = [generator.randrange(1 << 32) for _ in range(24)]
            canonical_codes = [canonical(code) for code in raw_codes]
            random_good = root / "random-good.u32le"
            random_good.write_bytes(
                b"".join(struct.pack("<I", code) for code in canonical_codes)
            )
            accepted_random = subprocess.run(
                [str(binary), str(random_good), str(len(canonical_codes)), "2"],
                text=True,
                capture_output=True,
            )
            self.assertEqual(accepted_random.returncode, 0, accepted_random.stderr)

            expected_bad = sum(
                code != minimum for code, minimum in zip(raw_codes, canonical_codes)
            )
            self.assertGreater(expected_bad, 0)
            random_bad = root / "random-bad.u32le"
            random_bad.write_bytes(
                b"".join(struct.pack("<I", code) for code in raw_codes)
            )
            rejected_random = subprocess.run(
                [str(binary), str(random_bad), str(len(raw_codes)), "2"],
                text=True,
                capture_output=True,
            )
            self.assertEqual(rejected_random.returncode, 1, rejected_random.stderr)
            self.assertEqual(
                json.loads(rejected_random.stdout)["noncanonical"], expected_bad
            )


if __name__ == "__main__":
    unittest.main()
