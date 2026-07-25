#!/usr/bin/env python3
"""Validate InfiniteDimensionalStatistics chapter specifications.

The loader accepts:
* a canonical self-contained chapter YAML;
* a package descriptor with one inventory file and one DAG file;
* a package inventory index whose ``inventory_files`` list contains readable
  section fragments.

The command is intentionally strict: all eight chapter descriptors must exist
and every loaded entry must satisfy the canonical declaration-level schema.
"""

from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
import sys
from typing import Any, Iterable

try:
    import yaml
except ImportError as exc:
    raise SystemExit(
        "PyYAML is required: install it with `python3 -m pip install PyYAML`."
    ) from exc


ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "InfiniteDimensionalStatistics"
SPEC_DIR = PROJECT / "Spec"
MANIFEST = PROJECT / "BookManifest.yaml"

VALID_PASSES = {"core", "starred", "exercise"}
VALID_DIFFICULTIES = {
    "routine",
    "substantial",
    "major-library",
    "research-level",
}


@dataclass(frozen=True)
class Problem:
    chapter: int | None
    location: str
    message: str

    def render(self) -> str:
        prefix = "global" if self.chapter is None else f"chapter {self.chapter}"
        return f"ERROR [{prefix}] {self.location}: {self.message}"


def load_yaml(path: Path) -> Any:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return yaml.safe_load(handle)
    except yaml.YAMLError as exc:
        raise ValueError(f"invalid YAML: {exc}") from exc


def mapping(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError(f"{where} must be a mapping")
    return value


def sequence(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise ValueError(f"{where} must be a list")
    return value


def nested(value: dict[str, Any], path: Iterable[str]) -> Any:
    current: Any = value
    for key in path:
        if not isinstance(current, dict) or key not in current:
            return None
        current = current[key]
    return current


def load_inventory_component(path: Path) -> dict[str, Any]:
    data = mapping(load_yaml(path), str(path))
    fragments = data.get("inventory_files")
    if fragments is None:
        return data
    fragment_names = sequence(fragments, f"{path}: inventory_files")
    merged: list[dict[str, Any]] = []
    for name in fragment_names:
        if not isinstance(name, str) or not name:
            raise ValueError(f"{path}: inventory fragment names must be strings")
        fragment_path = path.parent / name
        if not fragment_path.is_file():
            raise ValueError(f"inventory fragment does not exist: {fragment_path}")
        fragment = mapping(load_yaml(fragment_path), str(fragment_path))
        entries = sequence(fragment.get("inventory"), f"{fragment_path}: inventory")
        merged.extend(mapping(entry, f"{fragment_path}: inventory entry") for entry in entries)
    data = dict(data)
    data["inventory"] = merged
    return data


def resolve_package(
    descriptor_path: Path, descriptor: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, Any]]:
    package = descriptor.get("package")
    if not isinstance(package, dict):
        return descriptor, descriptor

    inventory_spec = mapping(
        package.get("declaration_inventory"), "package.declaration_inventory"
    )
    dag_spec = mapping(
        package.get("chapter_local_dependency_dag"),
        "package.chapter_local_dependency_dag",
    )
    inventory_name = inventory_spec.get("file")
    dag_name = dag_spec.get("file")
    if not isinstance(inventory_name, str) or not inventory_name:
        raise ValueError("package.declaration_inventory.file must be a nonempty string")
    if not isinstance(dag_name, str) or not dag_name:
        raise ValueError(
            "package.chapter_local_dependency_dag.file must be a nonempty string"
        )

    inventory_path = descriptor_path.parent / inventory_name
    dag_path = descriptor_path.parent / dag_name
    if not inventory_path.is_file():
        raise ValueError(f"inventory component does not exist: {inventory_path}")
    if not dag_path.is_file():
        raise ValueError(f"DAG component does not exist: {dag_path}")
    return (
        load_inventory_component(inventory_path),
        mapping(load_yaml(dag_path), str(dag_path)),
    )


def canonical_inventory(data: dict[str, Any]) -> list[dict[str, Any]]:
    entries = data.get("inventory")
    if isinstance(entries, list):
        return [mapping(item, "inventory entry") for item in entries]
    if "declaration_fields" in data and "declarations" in data:
        raise ValueError(
            "legacy compact declaration arrays are not accepted; "
            "convert to the canonical readable schema"
        )
    raise ValueError("no canonical top-level inventory list found")


def check_entry(chapter: int, index: int, entry: dict[str, Any]) -> list[Problem]:
    problems: list[Problem] = []
    location = f"inventory[{index}]"
    required_top = [
        "id",
        "kind",
        "book",
        "title",
        "statement",
        "hypotheses",
        "quantifier_order",
        "constants",
        "dependencies",
        "proof_status",
        "notes_status",
        "equivalents",
        "likely_lean_representation",
        "difficulty",
        "pass",
        "issues_for_central_review",
    ]
    for key in required_top:
        if key not in entry:
            problems.append(Problem(chapter, location, f"missing required field `{key}`"))

    identifier = entry.get("id")
    if not isinstance(identifier, str) or not identifier.strip():
        problems.append(Problem(chapter, location, "`id` must be a nonempty string"))

    required_nested = [
        ("book", "number"),
        ("book", "pages"),
        ("book", "section"),
        ("hypotheses", "explicit"),
        ("hypotheses", "implicit"),
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
    ]
    for path in required_nested:
        if nested(entry, path) is None:
            problems.append(
                Problem(chapter, location, f"missing required field `{'.'.join(path)}`")
            )

    notes = entry.get("notes_status")
    if isinstance(notes, dict):
        has_notes_flag = "discussed_or_extended_in_notes" in notes or any(
            key.startswith("discussed_or_extended_in_") for key in notes
        )
        if not has_notes_flag:
            problems.append(
                Problem(
                    chapter,
                    location,
                    "notes_status needs `discussed_or_extended_in_notes` or a documented legacy alias",
                )
            )

    for list_path in [
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
    ]:
        value = nested(entry, list_path)
        if value is not None and not isinstance(value, list):
            problems.append(
                Problem(chapter, location, f"`{'.'.join(list_path)}` must be a list")
            )

    pass_value = entry.get("pass")
    if pass_value not in VALID_PASSES:
        problems.append(Problem(chapter, location, f"invalid pass value: {pass_value!r}"))
    difficulty = entry.get("difficulty")
    if difficulty not in VALID_DIFFICULTIES:
        problems.append(
            Problem(chapter, location, f"invalid difficulty value: {difficulty!r}")
        )

    kind = str(entry.get("kind", "")).replace("_", " ").lower()
    if kind == "exercise":
        if pass_value != "exercise":
            problems.append(
                Problem(chapter, location, "exercise entry must use pass `exercise`")
            )
        reasons = entry.get("selection_reasons")
        if not isinstance(reasons, list) or not reasons:
            problems.append(
                Problem(
                    chapter,
                    location,
                    "exercise entry needs nonempty `selection_reasons`",
                )
            )
    elif pass_value == "exercise":
        problems.append(
            Problem(chapter, location, "non-exercise entry may not use pass `exercise`")
        )

    for exact_path in [
        ("equivalents", "mathlib", "exact_equivalent"),
        ("equivalents", "repository", "exact_equivalent"),
    ]:
        value = nested(entry, exact_path)
        if value is not None and not isinstance(value, bool):
            problems.append(
                Problem(chapter, location, f"`{'.'.join(exact_path)}` must be Boolean")
            )
    return problems


def canonical_dag(dag_data: dict[str, Any]) -> dict[str, Any]:
    dag = dag_data.get("chapter_local_dependency_dag", dag_data)
    return mapping(dag, "chapter_local_dependency_dag")


def dag_nodes(dag: dict[str, Any], default_nodes: list[str]) -> list[str]:
    raw = dag.get("nodes")
    if raw is None:
        # Compatibility for the accepted Chapter 4 package: isolated nodes are
        # inferred from the inventory. Repaired/new packages should list nodes.
        return list(default_nodes)
    raw = sequence(raw, "DAG nodes")
    if not all(isinstance(node, str) for node in raw):
        raise ValueError("all DAG nodes must be strings")
    return raw


def dag_edges(dag: dict[str, Any]) -> list[tuple[str, str]]:
    raw_edges = sequence(dag.get("edges"), "DAG edges")
    result: list[tuple[str, str]] = []
    for index, edge in enumerate(raw_edges):
        if isinstance(edge, dict):
            source, target = edge.get("from"), edge.get("to")
        elif isinstance(edge, list) and len(edge) >= 2:
            source, target = edge[0], edge[1]
        else:
            raise ValueError(f"DAG edge {index} has unsupported form")
        if not isinstance(source, str) or not isinstance(target, str):
            raise ValueError(f"DAG edge {index} endpoints must be strings")
        result.append((source, target))
    return result


def has_cycle(nodes: set[str], edges: list[tuple[str, str]]) -> bool:
    outgoing: dict[str, list[str]] = defaultdict(list)
    indegree = {node: 0 for node in nodes}
    for source, target in edges:
        outgoing[source].append(target)
        indegree[target] += 1
    queue = deque(node for node, degree in indegree.items() if degree == 0)
    visited = 0
    while queue:
        node = queue.popleft()
        visited += 1
        for target in outgoing[node]:
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    return visited != len(nodes)


def check_completeness(
    chapter: int, inventory_data: dict[str, Any]
) -> list[Problem]:
    problems: list[Problem] = []
    completeness = inventory_data.get("completeness_check")
    if not isinstance(completeness, dict):
        return [
            Problem(
                chapter,
                "completeness_check",
                "missing required numbered-label coverage metadata",
            )
        ]
    expected = completeness.get(
        "expected_numbered_labels",
        completeness.get("numbered_labels_expected"),
    )
    found = completeness.get(
        "found_numbered_labels",
        completeness.get("numbered_labels_found"),
    )
    missing = completeness.get("missing_numbered_labels")
    if not isinstance(expected, list):
        problems.append(
            Problem(chapter, "completeness_check", "expected labels must be a list")
        )
    if not isinstance(found, list):
        problems.append(
            Problem(chapter, "completeness_check", "found labels must be a list")
        )
    if not isinstance(missing, list):
        problems.append(
            Problem(chapter, "completeness_check", "missing labels must be a list")
        )
    elif missing:
        problems.append(
            Problem(chapter, "completeness_check", f"missing numbered labels: {missing}")
        )
    if isinstance(expected, list) and isinstance(found, list):
        absent = sorted(set(map(str, expected)) - set(map(str, found)))
        if absent:
            problems.append(
                Problem(
                    chapter,
                    "completeness_check",
                    f"expected labels absent from found-label list: {absent}",
                )
            )
    duplicates = completeness.get("duplicate_identifiers", [])
    if isinstance(duplicates, list) and duplicates:
        problems.append(
            Problem(
                chapter,
                "completeness_check",
                f"declared duplicate identifiers: {duplicates}",
            )
        )
    return problems


def check_chapter(chapter: int, path: Path) -> tuple[list[Problem], int, int]:
    problems: list[Problem] = []
    try:
        descriptor = mapping(load_yaml(path), str(path))
        inventory_data, dag_data = resolve_package(path, descriptor)
        inventory = canonical_inventory(inventory_data)
    except (OSError, ValueError) as exc:
        return [Problem(chapter, str(path.relative_to(ROOT)), str(exc))], 0, 0

    source_chapter = nested(descriptor, ("source", "chapter"))
    if source_chapter is not None and source_chapter != chapter:
        problems.append(
            Problem(chapter, "source.chapter", f"expected {chapter}, found {source_chapter}")
        )

    for index, entry in enumerate(inventory):
        problems.extend(check_entry(chapter, index, entry))

    identifiers = [
        entry.get("id") for entry in inventory if isinstance(entry.get("id"), str)
    ]
    identifier_set = set(identifiers)
    if len(identifiers) != len(identifier_set):
        counts: dict[str, int] = defaultdict(int)
        for identifier in identifiers:
            counts[identifier] += 1
        duplicates = sorted(key for key, count in counts.items() if count > 1)
        problems.append(
            Problem(chapter, "inventory", f"duplicate identifiers: {duplicates}")
        )

    for entry in inventory:
        identifier = entry.get("id")
        local_dependencies = nested(entry, ("dependencies", "chapter_local"))
        if isinstance(local_dependencies, list):
            for dependency in local_dependencies:
                if not isinstance(dependency, str) or dependency not in identifier_set:
                    problems.append(
                        Problem(
                            chapter,
                            str(identifier),
                            f"unresolved chapter-local dependency `{dependency}`",
                        )
                    )

    try:
        dag = canonical_dag(dag_data)
        nodes = dag_nodes(dag, identifiers)
        edges = dag_edges(dag)
    except ValueError as exc:
        problems.append(Problem(chapter, "dependency DAG", str(exc)))
        return problems, len(inventory), 0

    node_set = set(nodes)
    if len(nodes) != len(node_set):
        problems.append(Problem(chapter, "dependency DAG", "duplicate DAG nodes"))
    if node_set != identifier_set:
        missing_nodes = sorted(identifier_set - node_set)
        extra_nodes = sorted(node_set - identifier_set)
        if missing_nodes:
            problems.append(
                Problem(
                    chapter,
                    "dependency DAG",
                    f"inventory identifiers missing from DAG nodes: {missing_nodes}",
                )
            )
        if extra_nodes:
            problems.append(
                Problem(
                    chapter,
                    "dependency DAG",
                    f"DAG nodes absent from inventory: {extra_nodes}",
                )
            )

    for source, target in edges:
        if source not in identifier_set:
            problems.append(
                Problem(chapter, "dependency DAG", f"unknown source node `{source}`")
            )
        if target not in identifier_set:
            problems.append(
                Problem(chapter, "dependency DAG", f"unknown target node `{target}`")
            )
        if source == target:
            problems.append(
                Problem(chapter, "dependency DAG", f"self-loop at `{source}`")
            )

    valid_edges = [
        (source, target)
        for source, target in edges
        if source in identifier_set and target in identifier_set and source != target
    ]
    if has_cycle(identifier_set, valid_edges):
        problems.append(Problem(chapter, "dependency DAG", "directed cycle detected"))

    problems.extend(check_completeness(chapter, inventory_data))
    return problems, len(inventory), len(edges)


def main() -> int:
    problems: list[Problem] = []
    if not MANIFEST.is_file():
        problems.append(
            Problem(None, str(MANIFEST.relative_to(ROOT)), "missing manifest")
        )
    else:
        try:
            manifest = mapping(load_yaml(MANIFEST), str(MANIFEST))
            chapters = sequence(manifest.get("chapters"), "manifest chapters")
            manifest_numbers = {
                item.get("number") for item in chapters if isinstance(item, dict)
            }
            expected = set(range(1, 9))
            if manifest_numbers != expected:
                problems.append(
                    Problem(
                        None,
                        "BookManifest.yaml",
                        f"chapter numbers must be exactly 1..8, found {sorted(manifest_numbers)}",
                    )
                )
        except (OSError, ValueError) as exc:
            problems.append(Problem(None, "BookManifest.yaml", str(exc)))

    total_entries = 0
    total_edges = 0
    for chapter in range(1, 9):
        path = SPEC_DIR / f"Chapter{chapter:02d}.yaml"
        if not path.is_file():
            problems.append(
                Problem(
                    chapter,
                    str(path.relative_to(ROOT)),
                    "required specification is missing",
                )
            )
            continue
        chapter_problems, entries, edges = check_chapter(chapter, path)
        problems.extend(chapter_problems)
        total_entries += entries
        total_edges += edges

    if problems:
        for problem in problems:
            print(problem.render())
        print(
            f"FAILED: {len(problems)} error(s); "
            f"loaded {total_entries} entries and {total_edges} DAG edges."
        )
        return 1

    print(
        "PASS: all eight chapter specifications validated; "
        f"{total_entries} entries and {total_edges} DAG edges."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
