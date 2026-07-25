#!/usr/bin/env python3
"""Validate all eight InfiniteDimensionalStatistics chapter specifications.

Strict mode is the P1 acceptance gate. Migration flags exist only so an
incomplete repository can be audited without being mistaken for accepted work.
"""
from __future__ import annotations

import argparse
from collections import defaultdict, deque
import hashlib
from pathlib import Path
import re
from typing import Any

try:
    import yaml
except ImportError as exc:
    raise SystemExit("PyYAML is required: python3 -m pip install PyYAML") from exc

ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / "InfiniteDimensionalStatistics" / "Spec"
MANIFEST = ROOT / "InfiniteDimensionalStatistics" / "BookManifest.yaml"
VALID_PASSES = {"core", "starred", "exercise"}
VALID_DIFFICULTIES = {"routine", "substantial", "major-library", "research-level"}
NUMBERED = re.compile(
    r"((?:Definition|Lemma|Proposition|Theorem|Corollary|Example|Remark|Exercise|Item)\s+\d+\.\d+\.\d+)"
)
BLOCKING = re.compile(
    r"blocking|page[-_ ]image|needs?[-_ ](?:source|visual|direct)|untranscribed|to be recovered",
    re.I,
)


def parse_yaml(text: str, where: str) -> dict[str, Any]:
    try:
        value = yaml.safe_load(text)
    except yaml.YAMLError as exc:
        raise ValueError(f"invalid YAML in {where}: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{where}: top level must be a mapping")
    return value


def load(path: Path) -> dict[str, Any]:
    return parse_yaml(path.read_text(encoding="utf-8"), path.name)


def git_blob_sha(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()


def repaired_raw_inventory(doc: dict[str, Any], base: Path) -> dict[str, Any] | None:
    """Resolve an explicitly documented, byte-preserving raw inventory repair.

    This mechanism is only for a legacy assembled inventory whose original blob is
    retained as ``.txt``. Every changed line is declared in a valid YAML wrapper,
    checked against the original text, and applied before parsing. It must not be
    used to alter mathematical content or bypass source-fidelity checks.
    """

    repair = doc.get("raw_text_inventory")
    if repair is None:
        return None
    if not isinstance(repair, dict):
        raise ValueError("raw_text_inventory must be a mapping")

    filename = repair.get("file")
    if not isinstance(filename, str) or not filename:
        raise ValueError("raw_text_inventory.file must be a nonempty path")
    raw_path = base / filename
    if not raw_path.is_file():
        raise ValueError(f"missing raw inventory source {raw_path.name}")

    data = raw_path.read_bytes()
    expected_sha = repair.get("source_blob_sha")
    if expected_sha is not None:
        if not isinstance(expected_sha, str) or not expected_sha:
            raise ValueError("raw_text_inventory.source_blob_sha must be a nonempty string")
        actual_sha = git_blob_sha(data)
        if actual_sha != expected_sha:
            raise ValueError(
                f"raw inventory blob mismatch for {raw_path.name}: "
                f"expected {expected_sha}, found {actual_sha}"
            )

    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError(f"raw inventory source {raw_path.name} is not UTF-8") from exc

    replacements = repair.get("line_replacements")
    if not isinstance(replacements, list) or not replacements:
        raise ValueError("raw_text_inventory.line_replacements must be a nonempty list")

    lines = text.splitlines()
    parsed_replacements: list[tuple[int, str, list[str]]] = []
    seen_lines: set[int] = set()
    for index, item in enumerate(replacements):
        if not isinstance(item, dict):
            raise ValueError(f"raw repair[{index}] must be a mapping")
        line_number = item.get("line")
        expected = item.get("expected")
        replacement = item.get("replacement")
        if not isinstance(line_number, int) or line_number < 1:
            raise ValueError(f"raw repair[{index}].line must be a positive integer")
        if line_number in seen_lines:
            raise ValueError(f"duplicate raw repair line {line_number}")
        seen_lines.add(line_number)
        if not isinstance(expected, str):
            raise ValueError(f"raw repair[{index}].expected must be a string")
        if (
            not isinstance(replacement, list)
            or not replacement
            or not all(isinstance(value, str) for value in replacement)
        ):
            raise ValueError(
                f"raw repair[{index}].replacement must be a nonempty list of strings"
            )
        parsed_replacements.append((line_number, expected, replacement))

    # Descending order keeps the declared line numbers relative to the original blob.
    for line_number, expected, replacement in sorted(
        parsed_replacements, reverse=True
    ):
        offset = line_number - 1
        if offset >= len(lines):
            raise ValueError(
                f"raw repair line {line_number} exceeds {raw_path.name} length {len(lines)}"
            )
        if lines[offset] != expected:
            raise ValueError(
                f"raw repair line {line_number} mismatch in {raw_path.name}: "
                f"expected {expected!r}, found {lines[offset]!r}"
            )
        lines[offset : offset + 1] = replacement

    repaired_text = "\n".join(lines)
    if text.endswith("\n"):
        repaired_text += "\n"
    return parse_yaml(repaired_text, f"{raw_path.name} after declared transport repair")


def chapter_number(doc: dict[str, Any], path: Path) -> int:
    source = doc.get("source")
    value = source.get("chapter") if isinstance(source, dict) else None
    if isinstance(value, int):
        return value
    match = re.search(r"Chapter(\d{2})", path.name)
    if not match:
        raise ValueError("cannot determine chapter number")
    return int(match.group(1))


def component_names(meta: dict[str, Any], where: str) -> list[str]:
    one, many = meta.get("file"), meta.get("files")
    if one is not None and many is not None:
        raise ValueError(f"{where} must use either file or files")
    if isinstance(one, str) and one:
        return [one]
    if isinstance(many, list) and many and all(isinstance(x, str) and x for x in many):
        return many
    raise ValueError(f"{where} needs a nonempty file or files value")


def inventory_from_doc(doc: dict[str, Any], base: Path) -> list[dict[str, Any]]:
    repaired = repaired_raw_inventory(doc, base)
    if repaired is not None:
        return inventory_from_doc(repaired, base)

    fragments = doc.get("inventory_files")
    if fragments is not None:
        if not isinstance(fragments, list) or not all(isinstance(x, str) for x in fragments):
            raise ValueError("inventory_files must be a list of paths")
        rows: list[dict[str, Any]] = []
        for name in fragments:
            fragment_path = base / name
            if not fragment_path.is_file():
                raise ValueError(f"missing inventory fragment {fragment_path.name}")
            rows.extend(inventory_from_doc(load(fragment_path), fragment_path.parent))
        return rows
    rows = doc.get("inventory")
    if not isinstance(rows, list) or not all(isinstance(x, dict) for x in rows):
        raise ValueError("inventory must be a list of mappings")
    return rows


def load_chapter(
    path: Path,
) -> tuple[int, dict[str, Any], list[dict[str, Any]], dict[str, Any]]:
    descriptor = load(path)
    chapter = chapter_number(descriptor, path)
    if "declaration_fields" in descriptor and "declarations" in descriptor:
        raise ValueError("legacy compact positional schema is not accepted")
    package = descriptor.get("package")
    if not isinstance(package, dict):
        inventory = inventory_from_doc(descriptor, path.parent)
        dag = descriptor.get("chapter_local_dependency_dag")
        if not isinstance(dag, dict):
            raise ValueError("chapter_local_dependency_dag must be a mapping")
        return chapter, descriptor, inventory, dag

    inv_meta = package.get("declaration_inventory")
    dag_meta = package.get("chapter_local_dependency_dag")
    if not isinstance(inv_meta, dict) or not isinstance(dag_meta, dict):
        raise ValueError(
            "package needs declaration_inventory and chapter_local_dependency_dag mappings"
        )
    inventory: list[dict[str, Any]] = []
    component_docs: list[tuple[dict[str, Any], Path]] = []
    for name in component_names(inv_meta, "package.declaration_inventory"):
        component = path.parent / name
        if not component.is_file():
            raise ValueError(f"missing inventory component {component.name}")
        component_doc = load(component)
        component_docs.append((component_doc, component.parent))
        inventory.extend(inventory_from_doc(component_doc, component.parent))
    expected_entries = inv_meta.get("entry_count")
    if isinstance(expected_entries, int) and expected_entries != len(inventory):
        raise ValueError(
            f"inventory entry_count={expected_entries}, loaded={len(inventory)}"
        )

    effective_descriptor = dict(descriptor)
    if "completeness_check" not in effective_descriptor and len(component_docs) == 1:
        component_doc, component_base = component_docs[0]
        repaired = repaired_raw_inventory(component_doc, component_base)
        metadata_doc = repaired if repaired is not None else component_doc
        completeness = metadata_doc.get("completeness_check")
        if isinstance(completeness, dict):
            effective_descriptor["completeness_check"] = completeness

    dag_names = component_names(dag_meta, "package.chapter_local_dependency_dag")
    if len(dag_names) != 1:
        raise ValueError("DAG must use exactly one component")
    dag_path = path.parent / dag_names[0]
    if not dag_path.is_file():
        raise ValueError(f"missing DAG component {dag_path.name}")
    dag_doc = load(dag_path)
    key = dag_meta.get("key", "chapter_local_dependency_dag")
    dag = dag_doc.get(key, dag_doc)
    if not isinstance(dag, dict):
        raise ValueError("resolved DAG must be a mapping")
    return chapter, effective_descriptor, inventory, dag


def nested(entry: dict[str, Any], *keys: str) -> Any:
    value: Any = entry
    for key in keys:
        if not isinstance(value, dict) or key not in value:
            return None
        value = value[key]
    return value


def entry_errors(
    chapter: int,
    index: int,
    entry: dict[str, Any],
    allow_source_blockers: bool,
) -> list[str]:
    loc = f"chapter {chapter} inventory[{index}] ({entry.get('id', '?')})"
    errors: list[str] = []
    required = [
        ("id",),
        ("kind",),
        ("book", "number"),
        ("book", "pages"),
        ("book", "section"),
        ("title",),
        ("statement",),
        ("hypotheses", "explicit"),
        ("hypotheses", "implicit"),
        ("quantifier_order",),
        ("constants",),
        ("dependencies", "earlier_book"),
        ("dependencies", "chapter_local"),
        ("dependencies", "later_book_uses"),
        ("proof_status", "delegates_to_exercises"),
        ("proof_status", "contains_omitted_steps"),
        ("proof_status", "comment"),
        ("notes_status", "note_summary"),
        ("notes_status", "used_later_in_book"),
        ("equivalents", "mathlib", "status"),
        ("equivalents", "mathlib", "candidates"),
        ("equivalents", "mathlib", "exact_equivalent"),
        ("equivalents", "repository", "status"),
        ("equivalents", "repository", "candidates"),
        ("equivalents", "repository", "exact_equivalent"),
        ("likely_lean_representation", "sketch"),
        ("likely_lean_representation", "blockers"),
        ("difficulty",),
        ("pass",),
        ("issues_for_central_review",),
    ]
    for field in required:
        if nested(entry, *field) is None:
            errors.append(f"{loc}: missing {'.'.join(field)}")
    ident = entry.get("id")
    if not isinstance(ident, str) or not ident:
        errors.append(f"{loc}: id must be a nonempty string")
    list_fields = [
        ("book", "pages"),
        ("hypotheses", "explicit"),
        ("hypotheses", "implicit"),
        ("quantifier_order",),
        ("constants",),
        ("dependencies", "earlier_book"),
        ("dependencies", "chapter_local"),
        ("dependencies", "later_book_uses"),
        ("proof_status", "delegates_to_exercises"),
        ("equivalents", "mathlib", "candidates"),
        ("equivalents", "repository", "candidates"),
        ("likely_lean_representation", "blockers"),
        ("issues_for_central_review",),
    ]
    for field in list_fields:
        value = nested(entry, *field)
        if value is not None and not isinstance(value, list):
            errors.append(f"{loc}: {'.'.join(field)} must be a list")
    notes = entry.get("notes_status")
    if isinstance(notes, dict):
        flags = [
            key
            for key in notes
            if key == "discussed_or_extended_in_notes"
            or key.startswith("discussed_or_extended_in_")
        ]
        if not flags or not isinstance(notes[flags[0]], bool):
            errors.append(
                f"{loc}: notes_status needs a Boolean discussed_or_extended flag"
            )
    else:
        errors.append(f"{loc}: notes_status must be a mapping")
    pass_value, difficulty = entry.get("pass"), entry.get("difficulty")
    if pass_value not in VALID_PASSES:
        errors.append(f"{loc}: invalid pass {pass_value!r}")
    if difficulty not in VALID_DIFFICULTIES:
        errors.append(f"{loc}: invalid difficulty {difficulty!r}")
    kind = str(entry.get("kind", "")).replace("_", "-").lower()
    number = str(nested(entry, "book", "number") or "")
    section = str(nested(entry, "book", "section") or "")
    source_starred_value = entry.get("source_starred")
    if source_starred_value is not None and not isinstance(source_starred_value, bool):
        errors.append(f"{loc}: source_starred must be Boolean when present")
    source_starred = (
        "*" in number or "*" in section or source_starred_value is True
    )
    if kind == "exercise":
        if pass_value != "exercise":
            errors.append(f"{loc}: exercise must use exercise pass")
        reasons = entry.get("selection_reasons")
        if not isinstance(reasons, (dict, list)) or not reasons:
            errors.append(f"{loc}: selected exercise needs selection_reasons")
    elif pass_value == "exercise":
        errors.append(f"{loc}: non-exercise may not use exercise pass")
    if pass_value == "starred" and not source_starred:
        errors.append(
            f"{loc}: starred pass requires a starred declaration or enclosing section"
        )
    if source_starred and kind != "exercise" and pass_value != "starred":
        errors.append(f"{loc}: source-starred item must use starred pass")
    if not allow_source_blockers:
        statuses = [
            str(entry.get("transcription_status", "")),
            str(nested(entry, "source_fidelity", "transcription_status") or ""),
        ]
        blockers = " ".join(
            map(str, nested(entry, "likely_lean_representation", "blockers") or [])
        )
        statement = str(entry.get("statement", ""))
        if (
            any(BLOCKING.search(status) for status in statuses)
            or BLOCKING.search(blockers)
            or BLOCKING.search(statement)
        ):
            errors.append(f"{loc}: unresolved source-transcription blocker")
    return errors


def edge_pair(edge: Any) -> tuple[str, str]:
    if isinstance(edge, dict):
        source, target = edge.get("from"), edge.get("to")
    elif isinstance(edge, list) and len(edge) >= 2:
        source, target = edge[0], edge[1]
    else:
        raise ValueError("unsupported DAG edge")
    if not isinstance(source, str) or not isinstance(target, str):
        raise ValueError("DAG endpoints must be strings")
    return source, target


def cyclic(nodes: set[str], edges: list[tuple[str, str]]) -> bool:
    out: dict[str, list[str]] = defaultdict(list)
    indegree = {node: 0 for node in nodes}
    for source, target in edges:
        out[source].append(target)
        indegree[target] += 1
    queue = deque(node for node, degree in indegree.items() if degree == 0)
    seen = 0
    while queue:
        node = queue.popleft()
        seen += 1
        for target in out[node]:
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    return seen != len(nodes)


def validate_chapter(
    path: Path,
    allow_source_blockers: bool,
    allow_incomplete_coverage: bool,
) -> tuple[int, list[str], int, int]:
    chapter, descriptor, inventory, dag = load_chapter(path)
    errors: list[str] = []

    for field_name in ("blocking_source_transcriptions", "acceptance_blockers"):
        value = descriptor.get(field_name)
        if value is not None and not isinstance(value, list):
            errors.append(f"chapter {chapter}: {field_name} must be a list")
        elif value and not allow_source_blockers:
            errors.append(
                f"chapter {chapter}: unresolved descriptor blockers in {field_name}: {value}"
            )

    for index, entry in enumerate(inventory):
        errors.extend(entry_errors(chapter, index, entry, allow_source_blockers))
    ids = [entry.get("id") for entry in inventory if isinstance(entry.get("id"), str)]
    if len(ids) != len(set(ids)):
        errors.append(f"chapter {chapter}: duplicate inventory identifiers")
    idset = set(ids)
    for entry in inventory:
        for dep in nested(entry, "dependencies", "chapter_local") or []:
            if isinstance(dep, str) and dep not in idset:
                errors.append(
                    f"chapter {chapter} {entry.get('id')}: "
                    f"unknown chapter_local dependency {dep!r}"
                )
    raw_nodes = dag.get("nodes")
    nodes = set(ids) if raw_nodes is None else set(raw_nodes) if isinstance(raw_nodes, list) else set()
    if raw_nodes is not None and not isinstance(raw_nodes, list):
        errors.append(f"chapter {chapter}: DAG nodes must be a list")
    if nodes != idset:
        errors.append(f"chapter {chapter}: DAG node set does not exactly match inventory ids")
    try:
        edges = [edge_pair(edge) for edge in dag.get("edges", [])]
    except ValueError as exc:
        errors.append(f"chapter {chapter}: {exc}")
        edges = []
    seen_edges: set[tuple[str, str]] = set()
    for source, target in edges:
        if source not in idset or target not in idset:
            errors.append(
                f"chapter {chapter}: DAG edge references unknown node "
                f"{source!r}->{target!r}"
            )
        if source == target:
            errors.append(f"chapter {chapter}: DAG contains self-loop {source!r}")
        if (source, target) in seen_edges:
            errors.append(
                f"chapter {chapter}: duplicate DAG edge {source!r}->{target!r}"
            )
        seen_edges.add((source, target))
    if not errors and cyclic(idset, edges):
        errors.append(f"chapter {chapter}: dependency DAG contains a cycle")
    completeness = descriptor.get("completeness_check")
    gaps: list[Any] = []
    if isinstance(completeness, dict):
        for key in (
            "missing_numbered_labels",
            "apparent_numbering_gaps_requiring_source_check",
        ):
            value = completeness.get(key)
            if isinstance(value, list):
                gaps.extend(value)
    if gaps and not allow_incomplete_coverage:
        errors.append(
            f"chapter {chapter}: unresolved numbered-label coverage: "
            f"{sorted(set(map(str, gaps)))}"
        )
    labels = [
        match.group(1)
        for entry in inventory
        if (
            match := NUMBERED.match(
                str(nested(entry, "book", "number") or "")
            )
        )
    ]
    if len(labels) != len(set(labels)):
        errors.append(f"chapter {chapter}: duplicate numbered book labels")
    return chapter, errors, len(inventory), len(edges)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--allow-missing", action="store_true", help="migration audit only")
    parser.add_argument(
        "--allow-source-blockers", action="store_true", help="migration audit only"
    )
    parser.add_argument(
        "--allow-incomplete-coverage", action="store_true", help="migration audit only"
    )
    args = parser.parse_args()
    errors: list[str] = []
    reports: list[tuple[int, int, int]] = []
    if not MANIFEST.is_file():
        errors.append(f"missing {MANIFEST.relative_to(ROOT)}")
    else:
        try:
            manifest = load(MANIFEST)
            chapters = manifest.get("chapters")
            if not isinstance(chapters, list):
                errors.append("BookManifest.yaml: chapters must be a list")
            else:
                numbers = {
                    item.get("number") for item in chapters if isinstance(item, dict)
                }
                if numbers != set(range(1, 9)):
                    errors.append(
                        "BookManifest.yaml: chapter numbers must be exactly 1..8, "
                        f"found {sorted(numbers)}"
                    )
        except (ValueError, OSError) as exc:
            errors.append(f"BookManifest.yaml: {exc}")
    for chapter in range(1, 9):
        path = SPEC / f"Chapter{chapter:02d}.yaml"
        if not path.is_file():
            if not args.allow_missing:
                errors.append(f"chapter {chapter}: missing {path.relative_to(ROOT)}")
            continue
        try:
            number, chapter_errors, entries, edges = validate_chapter(
                path,
                args.allow_source_blockers,
                args.allow_incomplete_coverage,
            )
            errors.extend(chapter_errors)
            reports.append((number, entries, edges))
        except (ValueError, OSError) as exc:
            errors.append(f"chapter {chapter}: {exc}")
    for number, entries, edges in sorted(reports):
        print(f"Chapter {number}: loaded {entries} entries and {edges} dependency edges")
    if errors:
        print("\n".join(f"ERROR: {error}" for error in errors))
        return 1
    if args.allow_missing or args.allow_source_blockers or args.allow_incomplete_coverage:
        print("Loaded chapter specifications satisfy the selected migration-audit mode.")
    else:
        print("All eight chapter specifications satisfy the strict acceptance schema.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
