#!/usr/bin/env python3
from __future__ import annotations

import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]

AUDITS = {
    ROOT / "AnalysisI" / "SourceAudit.lean": 101,
    ROOT / "AnalysisII" / "SourceAudit.lean": 68,
}

for path, count in AUDITS.items():
    audit = path.read_text(encoding="utf-8")
    ids = [int(x) for x in re.findall(r"\bid := (\d+)", audit)]
    expected = list(range(1, count + 1))
    if ids != expected:
        raise SystemExit(f"{path.relative_to(ROOT)} IDs are not exactly 1..{count}: {ids}")

forbidden = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"^[ \t]*axiom\b", re.MULTILINE),
    "opaque": re.compile(r"^[ \t]*opaque\b", re.MULTILINE),
}
violations: list[str] = []
for path in sorted(ROOT.rglob("*.lean")):
    relative = path.relative_to(ROOT)
    if relative.parts and relative.parts[0] == ".lake":
        continue
    text = path.read_text(encoding="utf-8")
    for name, pattern in forbidden.items():
        if pattern.search(text):
            violations.append(f"{relative}: forbidden {name}")
if violations:
    raise SystemExit("\n".join(violations))

print(
    "OK: source inventories contain Analysis I IDs 1..101 and Analysis II "
    "IDs 1..68; no proof placeholders. Inventory size is not a correctness "
    "certificate; run check_analysis_ii_correctness.py --strict for Analysis II."
)
