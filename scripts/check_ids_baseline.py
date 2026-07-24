#!/usr/bin/env python3
"""Governance audit for the InfiniteDimensionalStatistics baseline.

The script is intentionally independent of GitHub Actions. Run it from the repository root before
`lake build`. It rejects proof escapes, validates the book-manifest schema, checks the skeleton's
local imports, and prints proposition-like structure fields with source locations.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
from dataclasses import dataclass

ROOT = pathlib.Path(__file__).resolve().parents[1]
IDS = ROOT / "InfiniteDimensionalStatistics"
MANIFEST = IDS / "BookManifest.yaml"

REQUIRED_MANIFEST_FIELDS = (
    "chapter",
    "section",
    "book_label",
    "page",
    "kind",
    "exact_statement",
    "lean_name",
    "lean_file",
    "dependencies",
    "mathlib_matches",
    "status",
    "statement_audited",
    "proof_audited",
    "axioms",
    "notes",
)

FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(
        r"^[ \t]*(?:(?:private|protected|public|noncomputable)\s+)*axiom\b", re.MULTILINE
    ),
    "opaque": re.compile(
        r"^[ \t]*(?:(?:private|protected|public|noncomputable)\s+)*opaque\b", re.MULTILINE
    ),
}

STRUCTURE_START = re.compile(
    r"^(?P<indent>[ \t]*)(?:(?:private|protected|public|noncomputable)\s+)*"
    r"(?:structure|class)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b(?P<tail>.*)$"
)
FIELD_START = re.compile(
    r"^(?P<indent>[ \t]+)(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*:\s*(?P<type>.*)$"
)
IMPORT = re.compile(r"^[ \t]*import[ \t]+(InfiniteDimensionalStatistics(?:\.[A-Za-z0-9_']+)+)", re.MULTILINE)

PROP_MARKERS = re.compile(
    r"(?:\bProp\b|\bNonempty\b|\.Nonempty\b|\bMeasurableSet\b|\bContinuous(?:On|At|WithinAt)?\b|"
    r"\bPairwise\b|\b(?:Function\.)?(?:Injective|Surjective|Bijective)\b|\bSummable\b|\bTendsto\b|"
    r"\b(?:Is|Has|Mem)[A-Z][A-Za-z0-9_']*\b|\bNodup\b|\bDisjoint\b|\bMonotone\b|\bAntitone\b|"
    r"\bCauchy\b|\bEqOn\b|\bMapsTo\b|[=≠≤≥∈⊆↔]|(?:^|\s)[<>](?:\s|$))"
)


@dataclass(frozen=True)
class StructureField:
    path: pathlib.Path
    line: int
    structure: str
    field: str
    type_text: str
    proposition_like: bool


def mask_comments_and_strings(text: str) -> str:
    """Replace comments and string contents by spaces while preserving newlines and offsets."""
    chars = list(text)
    out = list(text)
    i = 0
    block_depth = 0
    in_string = False
    escaped = False
    while i < len(chars):
        c = chars[i]
        nxt = chars[i + 1] if i + 1 < len(chars) else ""
        if block_depth:
            if c == "/" and nxt == "-":
                out[i] = out[i + 1] = " "
                block_depth += 1
                i += 2
                continue
            if c == "-" and nxt == "/":
                out[i] = out[i + 1] = " "
                block_depth -= 1
                i += 2
                continue
            if c != "\n":
                out[i] = " "
            i += 1
            continue
        if in_string:
            if c != "\n":
                out[i] = " "
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                in_string = False
            i += 1
            continue
        if c == "-" and nxt == "-":
            out[i] = out[i + 1] = " "
            i += 2
            while i < len(chars) and chars[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if c == "/" and nxt == "-":
            out[i] = out[i + 1] = " "
            block_depth = 1
            i += 2
            continue
        if c == '"':
            out[i] = " "
            in_string = True
            i += 1
            continue
        i += 1
    return "".join(out)


def indent_width(s: str) -> int:
    return len(s.expandtabs(2)) - len(s.lstrip(" \t").expandtabs(2))


def structure_fields(path: pathlib.Path, text: str) -> list[StructureField]:
    masked_lines = mask_comments_and_strings(text).splitlines()
    original_lines = text.splitlines()
    result: list[StructureField] = []
    i = 0
    while i < len(masked_lines):
        match = STRUCTURE_START.match(masked_lines[i])
        if not match:
            i += 1
            continue
        structure_name = match.group("name")
        base_indent = indent_width(match.group("indent"))
        header_parts = [match.group("tail")]
        header_end = i
        while "where" not in " ".join(header_parts) and header_end + 1 < len(masked_lines):
            header_end += 1
            header_parts.append(masked_lines[header_end].strip())
        header = " ".join(header_parts)
        prop_structure = bool(re.search(r":\s*Prop\b", header))

        j = header_end + 1
        fields: list[tuple[int, str, list[str]]] = []
        while j < len(masked_lines):
            line = masked_lines[j]
            if not line.strip():
                j += 1
                continue
            current_indent = indent_width(line)
            if current_indent <= base_indent:
                break
            field_match = FIELD_START.match(line)
            if field_match:
                fields.append((j, field_match.group("name"), [field_match.group("type").strip()]))
            elif fields:
                fields[-1][2].append(line.strip())
            j += 1

        for line_index, field_name, type_parts in fields:
            type_text = " ".join(part for part in type_parts if part).strip()
            proposition_like = prop_structure or bool(PROP_MARKERS.search(type_text))
            result.append(
                StructureField(
                    path=path,
                    line=line_index + 1,
                    structure=structure_name,
                    field=field_name,
                    type_text=type_text or original_lines[line_index].strip(),
                    proposition_like=proposition_like,
                )
            )
        i = max(j, i + 1)
    return result


def audit_forbidden(lean_files: list[pathlib.Path]) -> list[str]:
    violations: list[str] = []
    for path in lean_files:
        relative = path.relative_to(ROOT)
        text = mask_comments_and_strings(path.read_text(encoding="utf-8"))
        for name, pattern in FORBIDDEN.items():
            for match in pattern.finditer(text):
                line = text.count("\n", 0, match.start()) + 1
                violations.append(f"{relative}:{line}: forbidden {name}")
    return violations


def validate_manifest() -> list[str]:
    errors: list[str] = []
    if not MANIFEST.is_file():
        return [f"missing {MANIFEST.relative_to(ROOT)}"]
    text = MANIFEST.read_text(encoding="utf-8")
    for field in REQUIRED_MANIFEST_FIELDS:
        if not re.search(rf"^[ \t]*-[ \t]+{re.escape(field)}[ \t]*$", text, re.MULTILINE):
            errors.append(f"manifest required-field list is missing {field!r}")
        if not re.search(rf"^[ \t]+{re.escape(field)}:", text, re.MULTILINE):
            errors.append(f"manifest field definitions are missing {field!r}")
    if not re.search(r"^entries:[ \t]*\[\][ \t]*$", text, re.MULTILINE):
        errors.append("baseline manifest must contain no mathematical entries")
    return errors


def module_path(import_name: str) -> pathlib.Path:
    parts = import_name.split(".")
    if parts == ["InfiniteDimensionalStatistics"]:
        return ROOT / "InfiniteDimensionalStatistics.lean"
    return ROOT.joinpath(*parts).with_suffix(".lean")


def validate_imports() -> list[str]:
    errors: list[str] = []
    candidates = [ROOT / "InfiniteDimensionalStatistics.lean", *sorted(IDS.rglob("*.lean"))]
    for path in candidates:
        text = path.read_text(encoding="utf-8")
        for import_name in IMPORT.findall(mask_comments_and_strings(text)):
            target = module_path(import_name)
            if not target.is_file():
                errors.append(
                    f"{path.relative_to(ROOT)} imports missing module {import_name} "
                    f"({target.relative_to(ROOT)})"
                )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--all-structure-fields",
        action="store_true",
        help="print data fields as well as proposition-like structure fields",
    )
    args = parser.parse_args()

    lean_files = [
        p for p in sorted(ROOT.rglob("*.lean")) if ".lake" not in p.relative_to(ROOT).parts
    ]
    errors = audit_forbidden(lean_files) + validate_manifest() + validate_imports()

    fields: list[StructureField] = []
    for path in lean_files:
        fields.extend(structure_fields(path, path.read_text(encoding="utf-8")))

    selected = fields if args.all_structure_fields else [f for f in fields if f.proposition_like]
    heading = "all structure fields" if args.all_structure_fields else "proposition-like structure fields"
    print(f"Audit: {heading} ({len(selected)})")
    for field in selected:
        relative = field.path.relative_to(ROOT)
        print(
            f"{relative}:{field.line}: {field.structure}.{field.field} : {field.type_text}"
        )

    if errors:
        print("\nBaseline audit failed:", file=sys.stderr)
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print(
        f"\nOK: scanned {len(lean_files)} Lean files; no sorry/admit/axiom/opaque proof escapes; "
        "manifest schema and InfiniteDimensionalStatistics imports are valid."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
