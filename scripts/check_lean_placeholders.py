#!/usr/bin/env python3
"""Reject proof placeholders and extra trust primitives in tracked Lean code.

Comments and string literals are removed before token matching, so historical
phrases such as "sorry-free" do not create false positives.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


BANNED = re.compile(
    r"(?<![A-Za-z0-9_'])"
    r"(sorry|admit|native_decide|Lean\.ofReduceBool|axiom|unsafe)"
    r"(?![A-Za-z0-9_'])"
)


def strip_comments_and_strings(source: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_line = False
    in_string = False
    escaped = False

    while i < len(source):
        pair = source[i : i + 2]

        if in_line:
            if source[i] == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
            continue

        if in_string:
            if escaped:
                escaped = False
            elif source[i] == "\\":
                escaped = True
            elif source[i] == '"':
                in_string = False
            out.append("\n" if source[i] == "\n" else " ")
            i += 1
            continue

        if pair == "--":
            in_line = True
            out.extend("  ")
            i += 2
        elif pair == "/-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif source[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(source[i])
            i += 1

    if block_depth:
        raise ValueError("unterminated block comment")
    if in_string:
        raise ValueError("unterminated string literal")
    return "".join(out)


def tracked_lean_files() -> list[Path]:
    raw = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "*.lean"], text=False
    )
    files = [Path(item.decode()) for item in raw.split(b"\0") if item]
    return [path for path in files if path.as_posix() != "scripts/AxiomCheck.lean"]


def main() -> int:
    failures: list[str] = []
    files = tracked_lean_files()
    for path in files:
        try:
            stripped = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, ValueError) as exc:
            failures.append(f"{path}: scanner error: {exc}")
            continue
        for match in BANNED.finditer(stripped):
            line = stripped.count("\n", 0, match.start()) + 1
            failures.append(f"{path}:{line}: forbidden token {match.group(1)!r}")

    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"Placeholder scan passed for {len(files)} tracked Lean sources.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
