#!/usr/bin/env python3
"""Structural and reviewed-semantic audit for the Analysis II formalisation.

The audit has two modes:

* ``--baseline`` verifies the reproducibility of the present audit result. It
  exits successfully only while the repository still has exactly the reviewed
  full/partial/unmapped classification recorded below.
* ``--strict`` is the acceptance test. It exits successfully only when every
  one of the 68 source theorem-like environments has a reviewed, faithful Lean
  target.

The source is independently downloaded from a pinned commit, verified against
its Git blob SHA, rescanned for theorem-like environments, and compared with
``AnalysisII/SourceAudit.lean``.
"""

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
    "https://raw.githubusercontent.com/"
    f"{SOURCE_REPOSITORY}/{SOURCE_COMMIT_SHA}/{SOURCE_PATH}"
)
SOURCE_COUNT = 68

# Results of direct comparison against the pinned TeX statements. A result is
# ``full`` only when the existing Lean theorem proves the complete source
# statement (possibly in a genuine generalisation). ``partial`` means that a
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
# source 10. All other reviewed IDs must have their own sourceNNN declaration.
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
SOURCE_BEGIN_RE = re.compile(
    r"^\s*\\begin\{(?P<kind>thm|prop|lemma|cor)\}(?:\[[^\]]*\])?\s*$"
)
SOURCE_END_RE = re.compile(
    r"^\s*\\end\{(?P<kind>thm|prop|lemma|cor)\}\s*$"
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


def git_blob_sha(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()


def fetch_source_bytes(source_file: pathlib.Path | None) -> bytes:
    if source_file is not None:
        try:
            data = source_file.read_bytes()
        except OSError as exc:
            fail(f"cannot read source file {source_file}: {exc}")
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

    actual_sha = git_blob_sha(data)
    if actual_sha != SOURCE_BLOB_SHA:
        fail(
            "source blob hash mismatch: "
            f"found {actual_sha}, expected {SOURCE_BLOB_SHA}"
        )
    return data


def scan_source_entries(data: bytes) -> list[tuple[str, int, int]]:
    try:
        lines = data.decode("utf-8").splitlines()
    except UnicodeDecodeError as exc:
        fail(f"pinned Analysis II source is not UTF-8: {exc}")

    entries: list[tuple[str, int, int]] = []
    open_kind: str | None = None
    open_line: int | None = None

    for line_number, line in enumerate(lines, start=1):
        begin_match = SOURCE_BEGIN_RE.match(line)
        end_match = SOURCE_END_RE.match(line)

        if begin_match:
            if open_kind is not None:
                fail(
                    f"nested theorem-like environment at source line {line_number}"
                )
            open_kind = begin_match.group("kind")
            open_line = line_number
            continue

        if end_match:
            if open_kind is None or open_line is None:
                fail(
                    f"unmatched theorem-like environment end at source line {line_number}"
                )
            if end_match.group("kind") != open_kind:
                fail(
                    "mismatched theorem-like environment at source line "
                    f"{line_number}: opened {open_kind}, closed "
                    f"{end_match.group('kind')}"
                )
            entries.append((open_kind, open_line, line_number))
            open_kind = None
            open_line = None

    if open_kind is not None:
        fail(
            f"unclosed theorem-like environment {open_kind} from source line {open_line}"
        )
    if len(entries) != SOURCE_COUNT:
        fail(
            f"independent source scan found {len(entries)} theorem-like "
            f"environments, expected {SOURCE_COUNT}"
        )
    return entries


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


def compare_source_inventory(
    audited_entries: list[Entry],
    source_entries: list[tuple[str, int, int]],
) -> None:
    audited_triples = [
        (entry.kind, entry.start, entry.end) for entry in audited_entries
    ]
    if audited_triples == source_entries:
        return

    differences: list[str] = []
    for index, (audited, scanned) in enumerate(
        zip(audited_triples, source_entries), start=1
    ):
        if audited != scanned:
            differences.append(
                f"ID {index}: SourceAudit has {audited}, source scan has {scanned}"
            )
    if len(audited_triples) != len(source_entries):
        differences.append(
            f"entry counts differ: {len(audited_triples)} versus "
            f"{len(source_entries)}"
        )
    fail("source inventory does not match pinned TeX:\n" + "\n".join(differences))


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
    parser.add_argument(
        "--source-file",
        type=pathlib.Path,
        help="use a local copy of the pinned TeX source instead of downloading it",
    )
    args = parser.parse_args()

    entries = read_entries()
    source_data = fetch_source_bytes(args.source_file)
    source_entries = scan_source_entries(source_data)
    compare_source_inventory(entries, source_entries)

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
    check_count = len(
        re.findall(r"^[ \t]*#check\b", library_coverage, re.MULTILINE)
    )

    print("Analysis II deep correctness audit")
    print(f"  pinned source commit: {SOURCE_COMMIT_SHA}")
    print(f"  pinned source blob: {SOURCE_BLOB_SHA}")
    print(f"  independently scanned source environments: {len(source_entries)}")
    print(f"  SourceAudit theorem-like environments: {len(entries)}")
    print(f"  source-linked declarations: {len(declaration_names)}")
    print(f"  source-linked declaration IDs: {len(declaration_ids)}")
    print(f"  reviewed faithful source results: {len(FULL)}")
    print(f"  reviewed partial source results: {len(PARTIAL)}")
    print(
        "  source results without a verifiable declaration target: "
        f"{len(unmapped)}"
    )
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
