#!/usr/bin/env python3
"""Normalize Lean's `#print axioms` output for the public theorem audit."""

from __future__ import annotations

import pathlib
import re
import sys


THEOREMS = (
    "Gleason.busch",
    "Gleason.busch_born_rule",
    "Gleason.gleason",
    "Gleason.no_dispersion_free",
)
PATTERN = re.compile(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]")


def main(path: str) -> int:
    text = pathlib.Path(path).read_text(encoding="utf-8", errors="replace")
    if "sorryAx" in text:
        print("unexpected sorryAx dependency in Lean output", file=sys.stderr)
        return 1

    found: dict[str, str] = {}
    for name, dependencies in PATTERN.findall(text):
        if name in THEOREMS:
            if name in found:
                print(f"duplicate axiom report for {name}", file=sys.stderr)
                return 1
            normalized = ", ".join(part.strip() for part in dependencies.split(",") if part.strip())
            found[name] = f"[{normalized}]"

    missing = [name for name in THEOREMS if name not in found]
    if missing:
        print("missing axiom reports: " + ", ".join(missing), file=sys.stderr)
        return 1

    for name in THEOREMS:
        print(f"{name}: {found[name]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1]))
