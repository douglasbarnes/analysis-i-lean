#!/usr/bin/env python3
"""Structural and reviewed-semantic audit for the Analysis II formalisation.

The audit has two modes:

* ``--baseline`` verifies the reproducibility of the present audit result.  It
  exits successfully only while the repository still has exactly the reviewed
  full/partial/unmapped classification recorded below.
* ``--strict`` is the acceptance test.  It exits successfully only when every
  one of the 68 source theorem-like environments has a reviewed, faithful Lean
  target.

The source reviewed is ``dalcde/cam-notes/IB_M/analysis_ii.tex`` at blob
``1202516f75cf75afd8cb0cb2f33912a65fb4fcd0``.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
from dataclasses import dataclass

ROOT = pathlib.Path(__file__).resolve().parents[1]
COURSE = ROOT / "AnalysisII"
SOURCE_BLOB_SHA = "1202516f75cf75afd8cb0cb2f33912a65fb4fcd0"
SOURCE_COUNT = 68

# Results of direct comparison against the pinned TeX statements.  A result is
# ``full`` only when the existing Lean theorem proves the complete source
# statement (possibly in a genuine generalisation).  ``partial`` means that a
# declaration exists but omits a clause/direction or strengthens a hypothesis.
FULL: dict[int, str] = {
    10: "Heine--Cantor on a compact set generalises the closed-interval source theorem",
    28: "metric balls are open",
    39: "limits are unique in metric spaces",
    44: "singletons and finite subsets are closed",
    49: "compact-domain Heine--Cantor; mapped to source010_heineCantor",
    54: "uniqueness of the Frechet derivative",
    59: "Frechet chain rule",
}

PARTIAL: dict[int, str] = {
    1: (
        "the forward direction is present, but the reverse theorem assumes a "
        "pointwise limit instead of deriving existence of the limit from the "
        "uniform-Cauchy hypothesis for real-valued functions"
    ),
    2: (
        "the global uniform-limit theorem is present, but the source theorem "
        "only assumes continuity at one point of a subset; the local statement "
        "has not been formalised"
    ),
    41: (
        "arbitrary unions and binary intersections are present; the source also "
        "states arbitrary finite intersections and that the empty and whole "
        "spaces are open"
    ),
    43: (
        "arbitrary intersections and binary unions are present; the source also "
        "states arbitrary finite unions and that the empty and whole spaces are closed"
    ),
    52: (
        "the contraction case has a unique fixed point; the contracting-iterate "
        "declaration proves that one point is fixed by f but does not package or "
        "prove uniqueness for f as required by the source theorem"
    ),
    55: "only clauses (i) and (iv) of the seven-clause differentiability proposition are present",
    57: "only clause (iv) of the five-clause operator-norm proposition is present",
}

# Source 49 is deliberately implemented by the more general theorem named for
# source 10.  All other reviewed IDs must have their own sourceNNN declaration.
ALIASES: dict[int, str] = {49: "source010_heineCantor"}

EXPECTED_DECLARATION_IDS = {
    1,
    2,
    10,
    28,
    39,
    41,
    43,
    44,
    52,
    54,
    55,
    57,
    59,
}

ENTRY_RE = re.compile(
    r"\{\s*id := (?P<id>\d+),\s*lineStart := (?P<start>\d+),\s*"
    r"lineEnd := (?P<end>\d+),\s*kind := \"(?P<kind>[^\"]+)\",\s*"
    r"status := \.(?P<status>\w+)\s*\}"
)
DECL_RE = re.compile(
    r"\b(?:theorem|lemma|def|abbrev)\s+(?P<name>source(?P<id>\d{3})_[A-Za-z0-9_]+)"
)
FORBIDDEN_RE = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"^[ \t]*axiom\b", re.MULTILINE),
    "opaque": re.compile(r"^[ \t]*opaque\b", re.MULTILINE),
}


@dataclass(frozen=True)
class Entry:
    id: int
    start: int
    end: int
    kind: str
    status: str


def fail(message: str) -> None:
    raise SystemExit(f"Analysis II audit failure: {message}")


def read_entries() -> list[Entry]:
    text = (COURSE / "SourceAudit.lean").read_text(encoding="utf-8")
    entries = [
        Entry(
            id=int(match.group("id")),
            start=int(match.group("start")),
            end=int(match.group("end")),
            kind=match.group("kind"),
            status=match.group("status"),
        )
        for match in ENTRY_RE.finditer(text)
    ]
    if len(entries) != SOURCE_COUNT:
        fail(f"SourceAudit contains {len(entries)} entries, expected {SOURCE_COUNT}")
    if [entry.id for entry in entries] != list(range(1, SOURCE_COUNT + 1)):
        fail("SourceAudit IDs are not exactly 1..68 in source order")
    if any(entry.start > entry.end for entry in entries):
        fail("a SourceAudit line range is reversed")
    if any(left.end >= right.start for left, right in zip(entries, entries[1:])):
        fail("SourceAudit line ranges overlap or are not strictly source ordered")
    if {entry.kind for entry in entries} - {"thm", "prop", "lemma", "cor"}:
        fail("SourceAudit contains an unexpected theorem-like environment kind")
    return entries


def discover_declarations() -> tuple[set[int], set[str]]:
    ids: set[int] = set()
    names: set[str] = set()
    for path in sorted(COURSE.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for match in DECL_RE.finditer(text):
            ids.add(int(match.group("id")))
            names.add(match.group("name"))
    return ids, names


def check_forbidden_tokens() -> None:
    violations: list[str] = []
    for path in sorted(COURSE.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for name, pattern in FORBIDDEN_RE.items():
            if pattern.search(text):
                violations.append(f"{path.relative_to(ROOT)}: forbidden {name}")
    if violations:
        fail("\n".join(violations))


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--baseline", action="store_true")
    mode.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    entries = read_entries()
    declaration_ids, declaration_names = discover_declarations()
    check_forbidden_tokens()

    if declaration_ids != EXPECTED_DECLARATION_IDS:
        fail(
            "source-linked declaration IDs changed without updating the reviewed "
            f"audit: found {sorted(declaration_ids)}, expected "
            f"{sorted(EXPECTED_DECLARATION_IDS)}"
        )
    for source_id, target in ALIASES.items():
        if target not in declaration_names:
            fail(f"source {source_id} alias target {target} does not exist")

    reviewed = set(FULL) | set(PARTIAL)
    if set(FULL) & set(PARTIAL):
        fail("an ID is simultaneously classified full and partial")
    unmapped = set(range(1, SOURCE_COUNT + 1)) - reviewed

    library_coverage = (COURSE / "LibraryCoverage.lean").read_text(encoding="utf-8")
    check_count = len(re.findall(r"^[ \t]*#check\b", library_coverage, re.MULTILINE))

    print("Analysis II deep correctness audit")
    print(f"  pinned source blob: {SOURCE_BLOB_SHA}")
    print(f"  source theorem-like environments: {len(entries)}")
    print(f"  source-linked declaration IDs: {len(declaration_ids)}")
    print(f"  reviewed faithful source results: {len(FULL)}")
    print(f"  reviewed partial source results: {len(PARTIAL)}")
    print(f"  source results without a verifiable declaration target: {len(unmapped)}")
    print(f"  unlabelled Mathlib API #checks: {check_count}")
    print(f"  faithful IDs: {sorted(FULL)}")
    print(f"  partial IDs: {sorted(PARTIAL)}")
    print(f"  unmapped IDs: {sorted(unmapped)}")

    if args.baseline:
        if (len(FULL), len(PARTIAL), len(unmapped)) != (7, 7, 54):
            fail("the reviewed baseline counts changed unexpectedly")
        print("BASELINE RESULT: reproduced current incompleteness exactly")
        return 0

    if len(FULL) != SOURCE_COUNT:
        print("STRICT RESULT: FAIL")
        print("Every source result must move into FULL before this test can pass.")
        return 1

    print("STRICT RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
