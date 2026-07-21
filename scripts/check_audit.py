#!/usr/bin/env python3
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
audit = (ROOT / "AnalysisI" / "SourceAudit.lean").read_text(encoding="utf-8")
ids = [int(x) for x in re.findall(r"\bid := (\d+)", audit)]
expected = list(range(1, 102))
if ids != expected:
    raise SystemExit(f"audit IDs are not exactly 1..101: {ids}")

forbidden = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"^[ \t]*axiom\b", re.MULTILINE),
    "opaque": re.compile(r"^[ \t]*opaque\b", re.MULTILINE),
}
violations = []

for path in sorted(ROOT.rglob("*.lean")):
    if ".lake" in path.parts:
        continue
    text = path.read_text(encoding="utf-8")
    for name, pattern in forbidden.items():
        if pattern.search(text):
            violations.append(f"{path.relative_to(ROOT)}: forbidden {name}")
if violations:
    raise SystemExit("\n".join(violations))

print("OK: 101 sequential audit entries; no proof placeholders or proof-hiding declarations")
