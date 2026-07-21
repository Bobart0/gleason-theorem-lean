#!/usr/bin/env python3
"""Reject verification escape hatches in active Lean source.

The scanner blanks nested block comments, line comments, and string contents
before matching tokens, so ordinary documentation prose does not trigger it.
"""

from __future__ import annotations

import pathlib
import re
import sys


FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|sorryAx|axiom|postulate|unsafe|opaque|partial|extern|"
    r"implemented_by|native_decide)\b"
)


def active_source(text: str) -> str:
    out = list(text)
    i = 0
    block_depth = 0
    in_string = False

    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                out[i] = out[i + 1] = " "
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i] = out[i + 1] = " "
                block_depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif in_string:
            if text[i] == "\\" and i + 1 < len(text):
                out[i] = out[i + 1] = " "
                i += 2
            elif text[i] == '"':
                out[i] = " "
                in_string = False
                i += 1
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end == -1:
                end = len(text)
            for j in range(i, end):
                out[j] = " "
            i = end
        elif text.startswith("/-", i):
            out[i] = out[i + 1] = " "
            block_depth = 1
            i += 2
        elif text[i] == '"':
            out[i] = " "
            in_string = True
            i += 1
        else:
            i += 1

    if block_depth:
        raise ValueError("unterminated block comment")
    if in_string:
        raise ValueError("unterminated string literal")
    return "".join(out)


def main(paths: list[str]) -> int:
    failures: list[str] = []
    for raw_path in paths:
        path = pathlib.Path(raw_path)
        try:
            source = active_source(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, ValueError) as exc:
            failures.append(f"{path}: scanner error: {exc}")
            continue
        for match in FORBIDDEN.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            failures.append(f"{path}:{line}: forbidden active token: {match.group(0)}")

    if failures:
        print("Lean source verification failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print(f"Lean source scan passed ({len(paths)} tracked files).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
