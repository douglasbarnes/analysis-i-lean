#!/usr/bin/env python3
"""Source-pinned correctness audit for the Analysis II Lean library."""

from __future__ import annotations

import argparse
import hashlib
import pathlib
import re
import sys
import urllib.error
import urllib.request
from dataclasses import dataclass

ROOT = pathlib.Path(__file__).resolve().parents[1]
COURSE = ROOT / "AnalysisII"

SOURCE_REPOSITORY = "dalcde/cam-notes"
SOURCE_COMMIT_SHA = "0c1046b9244d84f65df513b14f22d26c51fd78b5"
SOURCE_PATH = "IB_M/analysis_ii.tex"
SOURCE_BLOB_SHA = "1202516f75cf75afd8cb0cb2f33912a65fb4fcd0"
SOURCE_URL = (
    f"https://raw.githubusercontent.com/{SOURCE_REPOSITORY}/"
    f"{SOURCE_COMMIT_SHA}/{SOURCE_PATH}"
)
SOURCE_COUNT = 68
ALL_SOURCE_IDS = set(range(1, SOURCE_COUNT + 1))

# A source result is FULL only if the current Lean theorem proves every clause
# of the source statement, or a genuine generalisation directly implies it.
FULL: dict[int, str] = {
    10: "Heine--Cantor on a compact set",
    28: "metric balls are open",
    39: "uniqueness of limits",
    44: "finite subsets are closed",
    49: "compact-domain Heine--Cantor, via source010_heineCantor",
    54: "uniqueness of the Frechet derivative",
    59: "Frechet chain rule",
}

# PARTIAL records a real declaration whose statement is insufficient.
PARTIAL: dict[int, str] = {
    1: (
        "reverse direction assumes a prescribed pointwise limit rather than "
        "deriving a real-valued uniform limit from uniform Cauchyness"
    ),
    2: (
        "global continuity theorem does not formalise the source's local "
        "continuity-at-a-point statement on a subset"
    ),
    41: "missing general finite intersections and the empty/whole-space clauses",
    43: "missing general finite unions and the empty/whole-space clauses",
    52: "contracting-iterate extension does not prove uniqueness for f",
    55: "only clauses (i) and (iv) of seven clauses are present",
    57: "only clause (iv) of five clauses is present",
}

ALIASES: dict[int, str] = {49: "source010_heineCantor"}
EXPECTED_DECLARATION_IDS = {
    1, 2, 10, 28, 39, 41, 43, 44, 52, 54, 55, 57, 59
}
EXPECTED_DECLARATION_NAMES = {
    "source001_uniformCauchySeqOn_of_tendstoUniformly",
    "source001_tendstoUniformly_of_uniformCauchySeqOn",
    "source002_uniform_limit_continuous",
    "source010_heineCantor",
    "source028_metric_ball_open",
    "source039_limit_unique",
    "source041_iUnion_open",
    "source041_inter_open",
    "source043_iInter_closed",
    "source043_union_closed",
    "source044_finite_closed",
    "source052_contraction_unique_fixedPoint",
    "source052_fixedPoint_of_contracting_iterate",
    "source054_fderiv_unique",
    "source055_fderiv_continuous",
    "source055_continuousLinearMap_derivative",
    "source057_apply_le_opNorm",
    "source059_chain_rule",
}

ENTRY_RE = re.compile(
    r"\{\s*id := (?P<id>\d+),\s*lineStart := (?P<start>\d+),\s*"
    r"lineEnd := (?P<end>\d+),\s*kind := \"(?P<kind>[^\"]+)\",\s*"
    r"status := \.(?P<status>\w+)\s*\}"
)
DECL_RE = re.compile(
    r"\b(?:theorem|lemma|def|abbrev)\s+"
    r"(?P<name>source(?P<id>\d{3})_[A-Za-z0-9_]+)"
)
# The source sometimes writes, for example, ``\begin{prop}\leavevmode``.
BEGIN_RE = re.compile(
    r"^\s*\\begin\{(?P<kind>thm|prop|lemma|cor)\}"
    r"(?:\[[^\]]*\])?.*$"
)
END_RE = re.compile(
    r"^\s*\\end\{(?P<kind>thm|prop|lemma|cor)\}.*$"
)
FORBIDDEN = {
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


def blob_sha(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()


def source_bytes(local_path: pathlib.Path | None) -> bytes:
    if local_path is not None:
        try:
            data = local_path.read_bytes()
        except OSError as exc:
            fail(f"cannot read source file {local_path}: {exc}")
    else:
        request = urllib.request.Request(
            SOURCE_URL,
            headers={"User-Agent": "analysis-ii-correctness-audit"},
        )
        try:
            with urllib.request.urlopen(request, timeout=60) as response:
                data = response.read()
        except (urllib.error.URLError, TimeoutError) as exc:
            fail(f"cannot download pinned Analysis II source: {exc}")

    actual = blob_sha(data)
    if actual != SOURCE_BLOB_SHA:
        fail(f"source blob hash is {actual}, expected {SOURCE_BLOB_SHA}")
    return data


def scan_tex(data: bytes) -> list[tuple[str, int, int]]:
    try:
        lines = data.decode("utf-8").splitlines()
    except UnicodeDecodeError as exc:
        fail(f"pinned source is not UTF-8: {exc}")

    result: list[tuple[str, int, int]] = []
    opened: tuple[str, int] | None = None

    for number, line in enumerate(lines, start=1):
        begin = BEGIN_RE.match(line)
        end = END_RE.match(line)

        if begin:
            if opened is not None:
                fail(f"nested theorem-like environment at source line {number}")
            opened = (begin.group("kind"), number)
            continue

        if end:
            if opened is None:
                fail(f"unmatched theorem-like environment end at line {number}")
            kind, start = opened
            if end.group("kind") != kind:
                fail(
                    f"environment opened as {kind} at line {start} but "
                    f"closed as {end.group('kind')} at line {number}"
                )
            result.append((kind, start, number))
            opened = None

    if opened is not None:
        fail(f"unclosed {opened[0]} environment from source line {opened[1]}")
    if len(result) != SOURCE_COUNT:
        fail(f"independent source scan found {len(result)} entries, expected 68")
    return result


def source_audit_entries() -> list[Entry]:
    text = (COURSE / "SourceAudit.lean").read_text(encoding="utf-8")
    entries = [
        Entry(
            id=int(m.group("id")),
            start=int(m.group("start")),
            end=int(m.group("end")),
            kind=m.group("kind"),
            status=m.group("status"),
        )
        for m in ENTRY_RE.finditer(text)
    ]
    if len(entries) != SOURCE_COUNT:
        fail(f"SourceAudit contains {len(entries)} entries, expected 68")
    if [entry.id for entry in entries] != list(range(1, SOURCE_COUNT + 1)):
        fail("SourceAudit IDs are not exactly 1..68 in source order")
    if any(entry.start > entry.end for entry in entries):
        fail("a SourceAudit line range is reversed")
    if any(a.end >= b.start for a, b in zip(entries, entries[1:])):
        fail("SourceAudit ranges overlap or are not strictly ordered")
    if {entry.kind for entry in entries} - {"thm", "prop", "lemma", "cor"}:
        fail("SourceAudit contains an unexpected environment kind")
    return entries


def check_inventory(entries: list[Entry], scanned: list[tuple[str, int, int]]) -> None:
    recorded = [(entry.kind, entry.start, entry.end) for entry in entries]
    if recorded == scanned:
        return

    differences = [
        f"ID {i}: SourceAudit={left}, TeX={right}"
        for i, (left, right) in enumerate(zip(recorded, scanned), start=1)
        if left != right
    ]
    if len(recorded) != len(scanned):
        differences.append(f"counts differ: {len(recorded)} versus {len(scanned)}")
    fail("inventory differs from pinned TeX:\n" + "\n".join(differences))


def declarations() -> tuple[set[int], set[str]]:
    ids: set[int] = set()
    names: set[str] = set()
    for path in sorted(COURSE.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for match in DECL_RE.finditer(text):
            ids.add(int(match.group("id")))
            names.add(match.group("name"))
    return ids, names


def check_proof_escapes() -> None:
    violations: list[str] = []
    for path in sorted(COURSE.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for token, pattern in FORBIDDEN.items():
            if pattern.search(text):
                violations.append(f"{path.relative_to(ROOT)}: forbidden {token}")
    if violations:
        fail("\n".join(violations))


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--baseline", action="store_true")
    mode.add_argument("--strict", action="store_true")
    parser.add_argument(
        "--source-file",
        type=pathlib.Path,
        help="use a local source copy; its Git blob hash is still verified",
    )
    args = parser.parse_args()

    entries = source_audit_entries()
    scanned = scan_tex(source_bytes(args.source_file))
    check_inventory(entries, scanned)

    declaration_ids, declaration_names = declarations()
    check_proof_escapes()

    if declaration_ids != EXPECTED_DECLARATION_IDS:
        fail(
            "source-linked declaration IDs changed without review: "
            f"found {sorted(declaration_ids)}, "
            f"expected {sorted(EXPECTED_DECLARATION_IDS)}"
        )
    if declaration_names != EXPECTED_DECLARATION_NAMES:
        fail(
            "source-linked declaration names changed without review: "
            f"found {sorted(declaration_names)}, "
            f"expected {sorted(EXPECTED_DECLARATION_NAMES)}"
        )
    for source_id, target in ALIASES.items():
        if target not in declaration_names:
            fail(f"source {source_id} alias target {target} does not exist")

    if set(FULL) & set(PARTIAL):
        fail("an ID is classified both full and partial")
    reviewed = set(FULL) | set(PARTIAL)
    if reviewed - ALL_SOURCE_IDS:
        fail(f"review contains out-of-range source IDs: {sorted(reviewed - ALL_SOURCE_IDS)}")
    unmapped = ALL_SOURCE_IDS - reviewed

    library_coverage = (COURSE / "LibraryCoverage.lean").read_text(encoding="utf-8")
    api_checks = len(
        re.findall(r"^[ \t]*#check\b", library_coverage, re.MULTILINE)
    )

    print("Analysis II deep correctness audit")
    print(f"  pinned source commit: {SOURCE_COMMIT_SHA}")
    print(f"  pinned source blob: {SOURCE_BLOB_SHA}")
    print(f"  independently scanned source environments: {len(scanned)}")
    print(f"  SourceAudit environments: {len(entries)}")
    print(f"  source-linked declarations: {len(declaration_names)}")
    print(f"  source-linked declaration IDs: {len(declaration_ids)}")
    print(f"  fully verified results: {len(FULL)}")
    print(f"  partial results: {len(PARTIAL)}")
    print(f"  unmapped results: {len(unmapped)}")
    print(f"  unlabelled Mathlib API #checks: {api_checks}")
    print(f"  full IDs: {sorted(FULL)}")
    print(f"  partial IDs: {sorted(PARTIAL)}")
    print(f"  unmapped IDs: {sorted(unmapped)}")

    if args.baseline:
        if (len(FULL), len(PARTIAL), len(unmapped)) != (7, 7, 54):
            fail("reviewed baseline counts changed unexpectedly")
        print("BASELINE RESULT: reproduced current incompleteness exactly")
        return 0

    if set(FULL) != ALL_SOURCE_IDS or PARTIAL:
        print("STRICT RESULT: FAIL")
        print("All and only source IDs 1..68 must be FULL before this test can pass.")
        return 1

    print("STRICT RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
