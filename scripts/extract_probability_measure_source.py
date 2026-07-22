#!/usr/bin/env python3
from __future__ import annotations

import bisect
import json
import re
import urllib.request
from collections import Counter
from pathlib import Path

SOURCE_URL = (
    "https://raw.githubusercontent.com/dalcde/cam-notes/master/"
    "II_M/probability_and_measure.tex"
)
OUTPUT = Path("probability-measure-envs.json")
EXPECTED_ENVIRONMENTS = 136


def line_starts(text: str) -> list[int]:
    starts = [0]
    starts.extend(match.end() for match in re.finditer(r"\n", text))
    return starts


def extract(text: str) -> list[dict[str, object]]:
    starts = line_starts(text)

    def line_no(offset: int) -> int:
        return bisect.bisect_right(starts, offset)

    pattern = re.compile(
        r"\\begin\{(defi|thm|prop|lemma|cor|notation)\}(?:\[[^\n]*?\])?"
    )
    matches = list(pattern.finditer(text))
    entries: list[dict[str, object]] = []

    for zero_index, match in enumerate(matches):
        index = zero_index + 1
        kind = match.group(1)
        end_match = re.search(rf"\\end\{{{kind}\}}", text[match.end() :])
        if end_match is None:
            raise RuntimeError(f"missing end for {kind} at line {line_no(match.start())}")
        environment_end = match.end() + end_match.end()
        next_start = matches[zero_index + 1].start() if zero_index + 1 < len(matches) else len(text)

        proof = None
        proof_line_start = None
        proof_line_end = None
        between = text[environment_end:next_start]
        proof_match = re.search(r"\\begin\{proof\}(?:\[[^\n]*?\])?", between)
        if proof_match is not None:
            proof_start = environment_end + proof_match.start()
            proof_close = re.search(r"\\end\{proof\}", text[proof_start:next_start])
            if proof_close is not None:
                proof_end = proof_start + proof_close.end()
                proof = text[proof_start:proof_end]
                proof_line_start = line_no(proof_start)
                proof_line_end = line_no(proof_end)

        entries.append(
            {
                "id": index,
                "kind": kind,
                "line_start": line_no(match.start()),
                "line_end": line_no(environment_end),
                "statement": text[match.start() : environment_end],
                "proof_line_start": proof_line_start,
                "proof_line_end": proof_line_end,
                "proof": proof,
            }
        )
    return entries


def main() -> None:
    with urllib.request.urlopen(SOURCE_URL) as response:
        text = response.read().decode("utf-8")
    entries = extract(text)
    if len(entries) != EXPECTED_ENVIRONMENTS:
        raise RuntimeError(
            f"expected {EXPECTED_ENVIRONMENTS} labelled environments, found {len(entries)}"
        )
    OUTPUT.write_text(json.dumps(entries, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"extracted {len(entries)} labelled environments")
    print(Counter(entry["kind"] for entry in entries))


if __name__ == "__main__":
    main()
