#!/usr/bin/env python3
"""Validate the eight InfiniteDimensionalStatistics chapter specifications."""
from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict, deque
from pathlib import Path
from typing import Any, Mapping

try:
    import yaml
except ImportError as exc:
    raise SystemExit(
        "PyYAML is required. Run: python3 -m pip install -r scripts/requirements-spec.txt"
    ) from exc

PASSES = {"core", "starred", "exercise"}
DIFFICULTIES = {"routine", "substantial", "major-library", "research-level"}
UNRESOLVED = [
    r"\bto be transcribed\b",
    r"\bneeds? to be transcribed\b",
    r"\bnot recoverable\b",
    r"\brecoverable statement\b",
    r"\bschematic(?:ally)?\b",
    r"\btemplate\b",
    r"\bexact .* requires direct .* transcription\b",
    r"\bexact .* must be transcribed\b",
]


def mapping(value: Any) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def first(record: Mapping[str, Any], *keys: str) -> Any:
    for key in keys:
        if key in record:
            return record[key]
    return None


def nested(record: Mapping[str, Any], *paths: tuple[str, ...]) -> Any:
    for path in paths:
        value: Any = record
        for key in path:
            if not isinstance(value, Mapping) or key not in value:
                break
            value = value[key]
        else:
            return value
    return None


def load(path: Path) -> Any:
    with path.open(encoding="utf-8") as handle:
        return yaml.safe_load(handle)


def decode_compact(raw: Mapping[str, Any]) -> list[dict[str, Any]]:
    fields = raw.get("declaration_fields")
    rows = raw.get("declarations")
    node_ids = raw.get("node_ids")
    if not all(isinstance(value, list) for value in (fields, rows, node_ids)):
        return []
    enums = mapping(mapping(raw.get("normalisation")).get("enums"))
    entries: list[dict[str, Any]] = []
    for index, row in enumerate(rows):
        if not isinstance(row, list) or len(row) != len(fields):
            continue
        item = dict(zip(fields, row))
        node = item.get("node")
        item["id"] = node_ids[node] if isinstance(node, int) and 0 <= node < len(node_ids) else f"row-{index}"
        for field in ("section", "kind", "expected_difficulty", "pass"):
            table = mapping(enums.get(field))
            value = item.get(field)
            if isinstance(value, int):
                item[field] = table.get(str(value), value)
        entries.append(item)
    return entries


def graph(raw: Any) -> tuple[list[str], list[tuple[str, str]]]:
    dag = mapping(raw)
    nodes: list[str] = []
    for node in dag.get("nodes", []) or []:
        if isinstance(node, str):
            nodes.append(node)
        elif isinstance(node, Mapping) and isinstance(node.get("id"), str):
            nodes.append(node["id"])
    edges: list[tuple[str, str]] = []
    for edge in dag.get("edges", []) or []:
        if isinstance(edge, Mapping):
            source, target = first(edge, "from", "source", "prerequisite"), first(edge, "to", "target", "dependent")
        elif isinstance(edge, list) and len(edge) >= 2:
            source, target = edge[0], edge[1]
        else:
            continue
        if isinstance(source, str) and isinstance(target, str):
            edges.append((source, target))
    return nodes, edges


def load_package(path: Path) -> tuple[Mapping[str, Any], list[Mapping[str, Any]], list[str], list[tuple[str, str]], bool]:
    raw = load(path)
    if not isinstance(raw, Mapping):
        raise ValueError(f"{path}: top-level value must be a mapping")
    package = raw.get("package")
    if isinstance(package, Mapping):
        inv_cfg = mapping(package.get("declaration_inventory"))
        dag_cfg = mapping(package.get("chapter_local_dependency_dag"))
        inventory = load(path.parent / str(inv_cfg.get("file", "")))
        dag = load(path.parent / str(dag_cfg.get("file", "")))
        entries = list(mapping(inventory).get(str(inv_cfg.get("key", "inventory")), []) or [])
        nodes, edges = graph(dag)
        if not nodes:
            nodes = [str(item.get("id")) for item in entries if isinstance(item, Mapping)]
        return raw, entries, nodes, edges, False
    if isinstance(raw.get("declaration_fields"), list):
        entries = decode_compact(raw)
        nodes = [item for item in raw.get("node_ids", []) if isinstance(item, str)]
        dag_nodes, edges = graph(raw.get("dependency_dag"))
        return raw, entries, dag_nodes or nodes, edges, True
    entries: list[Mapping[str, Any]] = []
    for key in ("declarations", "exercises", "inventory"):
        value = raw.get(key)
        if isinstance(value, list):
            entries.extend(item for item in value if isinstance(item, Mapping))
    nodes, edges = graph(raw.get("dependency_dag"))
    if not nodes:
        nodes = [str(item.get("id")) for item in entries if isinstance(item.get("id"), str)]
    return raw, entries, nodes, edges, False


def book_number(entry: Mapping[str, Any]) -> Any:
    return nested(entry, ("book", "number"), ("book_number",), ("book_label",))


def pages(entry: Mapping[str, Any]) -> Any:
    return nested(entry, ("book", "pages"), ("book_page",), ("pages",), ("page",))


def section(entry: Mapping[str, Any]) -> Any:
    return nested(entry, ("book", "section"), ("section",))


def statement(entry: Mapping[str, Any]) -> Any:
    value = first(entry, "statement", "precise_statement", "mathematical_statement")
    if isinstance(value, Mapping):
        return first(value, "as_printed_or_read", "text", "statement")
    return value


def pass_value(entry: Mapping[str, Any]) -> Any:
    return first(entry, "pass", "formalisation_pass")


def difficulty(entry: Mapping[str, Any]) -> Any:
    return first(entry, "difficulty", "expected_difficulty")


def equivalence(entry: Mapping[str, Any]) -> Any:
    return first(entry, "equivalents", "equivalence", "matches")


def direct_equivalence_complete(entry: Mapping[str, Any]) -> bool:
    audit = equivalence(entry)
    if not isinstance(audit, Mapping):
        return False
    for side in ("mathlib", "repository"):
        record = mapping(audit.get(side))
        if not isinstance(record.get("status"), str):
            return False
        if not isinstance(record.get("candidates"), list):
            return False
        if not isinstance(record.get("exact_equivalent"), bool):
            return False
    return True


def required_missing(entry: Mapping[str, Any]) -> list[str]:
    checks = {
        "book number/label": book_number(entry),
        "page": pages(entry),
        "section": section(entry),
        "statement": statement(entry),
        "hypotheses": first(entry, "hypotheses", "explicit_hypotheses", "implicit_hypotheses"),
        "constants/quantifier order": first(entry, "constants_and_quantifier_order", "quantifier_order", "constants"),
        "dependencies": entry.get("dependencies"),
        "proof delegation": first(entry, "proof_delegation", "proof_status", "proof", "proof_delegation_to_exercises"),
        "notes/later-use status": first(entry, "notes_status", "notes_and_later_use", "notes_result_used_later"),
        "likely Lean representation": first(entry, "likely_lean", "likely_lean_representation"),
        "difficulty": difficulty(entry),
        "pass": pass_value(entry),
    }
    return [name for name, value in checks.items() if value is None]


def validate_graph(chapter: int, nodes: list[str], edges: list[tuple[str, str]], errors: list[str]) -> None:
    node_set = set(nodes)
    if len(node_set) != len(nodes):
        errors.append(f"Chapter {chapter:02d}: duplicate DAG node ids")
    adjacency: dict[str, list[str]] = defaultdict(list)
    indegree = {node: 0 for node in nodes}
    for source, target in edges:
        if source not in node_set or target not in node_set:
            errors.append(f"Chapter {chapter:02d}: DAG edge {source!r}->{target!r} has a missing endpoint")
            continue
        adjacency[source].append(target)
        indegree[target] += 1
    queue = deque(node for node in nodes if indegree[node] == 0)
    visited = 0
    while queue:
        node = queue.popleft()
        visited += 1
        for target in adjacency[node]:
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    if visited != len(nodes):
        errors.append(f"Chapter {chapter:02d}: dependency graph contains a cycle")


def validate_chapter(path: Path, chapter_record: Mapping[str, Any], errors: list[str]) -> None:
    chapter = int(chapter_record["number"])
    raw, entries, nodes, edges, legacy = load_package(path)
    if legacy:
        errors.append(f"Chapter {chapter:02d}: legacy compact schema is diagnostic-only; convert it to readable canonical YAML")
    ids: list[str] = []
    for index, entry in enumerate(entries):
        identifier = entry.get("id")
        label = identifier if isinstance(identifier, str) else f"entry[{index}]"
        if not isinstance(identifier, str) or not identifier:
            errors.append(f"Chapter {chapter:02d}: {label} has no nonempty id")
        else:
            ids.append(identifier)
        missing = required_missing(entry)
        if missing:
            errors.append(f"Chapter {chapter:02d} {label}: missing required fields: {', '.join(missing)}")
        if pass_value(entry) not in PASSES:
            errors.append(f"Chapter {chapter:02d} {label}: invalid pass {pass_value(entry)!r}")
        if difficulty(entry) not in DIFFICULTIES:
            errors.append(f"Chapter {chapter:02d} {label}: invalid difficulty {difficulty(entry)!r}")
        text = statement(entry)
        if not isinstance(text, str):
            errors.append(f"Chapter {chapter:02d} {label}: statement is not a string")
        else:
            for pattern in UNRESOLVED:
                if re.search(pattern, text.lower()):
                    errors.append(f"Chapter {chapter:02d} {label}: unresolved transcription marker {pattern!r}")
                    break
        if not direct_equivalence_complete(entry):
            errors.append(
                f"Chapter {chapter:02d} {label}: equivalence audit must directly provide status, candidates, and exact_equivalent for mathlib and repository"
            )
    duplicates = sorted(item for item in set(ids) if ids.count(item) > 1)
    if duplicates:
        errors.append(f"Chapter {chapter:02d}: duplicate inventory ids: {', '.join(duplicates)}")
    if not nodes:
        errors.append(f"Chapter {chapter:02d}: no dependency DAG nodes found")
    else:
        id_set, node_set = set(ids), set(nodes)
        missing_nodes = sorted(id_set - node_set)
        extra_nodes = sorted(node_set - id_set)
        if missing_nodes:
            errors.append(f"Chapter {chapter:02d}: inventory ids absent from DAG: {', '.join(missing_nodes)}")
        if extra_nodes:
            errors.append(f"Chapter {chapter:02d}: DAG nodes absent from inventory: {', '.join(extra_nodes)}")
        validate_graph(chapter, nodes, edges, errors)
    starred_sections = chapter_record.get("book_starred_sections")
    if isinstance(starred_sections, list):
        for entry in entries:
            if pass_value(entry) != "starred":
                continue
            current = str(section(entry) or "")
            if not any(current == prefix or current.startswith(prefix + ".") for prefix in starred_sections):
                errors.append(
                    f"Chapter {chapter:02d} {entry.get('id')}: starred pass is not justified by a book-starred section; difficulty must not determine pass"
                )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--allow-missing", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    project = root / "InfiniteDimensionalStatistics"
    manifest_path = project / "BookManifest.yaml"
    try:
        manifest = load(manifest_path)
    except (OSError, yaml.YAMLError, ValueError) as exc:
        print(f"ERROR: {exc}")
        return 2
    chapters = mapping(manifest).get("chapters")
    errors: list[str] = []
    warnings: list[str] = []
    if not isinstance(chapters, list) or len(chapters) != 8:
        errors.append("BookManifest.yaml must contain exactly eight chapter records")
        chapters = []
    seen: set[int] = set()
    for record in chapters:
        if not isinstance(record, Mapping) or not isinstance(record.get("number"), int):
            errors.append("BookManifest.yaml contains an invalid chapter record")
            continue
        chapter = int(record["number"])
        if chapter in seen or chapter not in range(1, 9):
            errors.append(f"BookManifest.yaml has invalid or duplicate chapter number {chapter}")
            continue
        seen.add(chapter)
        relative = record.get("spec")
        if not isinstance(relative, str):
            errors.append(f"Chapter {chapter:02d}: manifest spec path is missing")
            continue
        path = project / relative
        if not path.exists():
            message = f"Chapter {chapter:02d}: missing specification entry point {path.relative_to(root)}"
            (warnings if args.allow_missing else errors).append(message)
            continue
        try:
            validate_chapter(path, record, errors)
        except (OSError, yaml.YAMLError, ValueError) as exc:
            errors.append(str(exc))
    for warning in warnings:
        print(f"WARNING: {warning}")
    for error in errors:
        print(f"ERROR: {error}")
    if errors:
        print(f"\nValidation failed with {len(errors)} error(s).")
        return 1
    print("All InfiniteDimensionalStatistics chapter specifications passed validation.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
