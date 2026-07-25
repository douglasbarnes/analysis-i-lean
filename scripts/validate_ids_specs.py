#!/usr/bin/env python3
"""Validate all InfiniteDimensionalStatistics chapter specification packages."""

from collections import Counter, defaultdict, deque
from pathlib import Path
import sys

try:
    import yaml
except ImportError as exc:
    raise SystemExit("PyYAML is required (`python3 -m pip install PyYAML`).") from exc

ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / "InfiniteDimensionalStatistics" / "Spec"
MANIFEST = ROOT / "InfiniteDimensionalStatistics" / "BookManifest.yaml"
PASSES = {"core", "starred", "exercise"}
DIFFICULTIES = {"routine", "substantial", "major-library", "research-level"}

ENTRY_FIELDS = {
    "id", "kind", "book", "title", "statement", "hypotheses",
    "quantifier_order", "constants", "dependencies", "proof_status",
    "notes_status", "equivalents", "likely_lean_representation",
    "difficulty", "pass", "issues_for_central_review",
}
NESTED_FIELDS = (
    ("book", "number"), ("book", "pages"), ("book", "section"),
    ("hypotheses", "explicit"), ("hypotheses", "implicit"),
    ("dependencies", "earlier_book"), ("dependencies", "chapter_local"),
    ("dependencies", "later_book_uses"),
    ("proof_status", "delegates_to_exercises"),
    ("proof_status", "contains_omitted_steps"), ("proof_status", "comment"),
    ("notes_status", "discussed_or_extended_in_notes"),
    ("notes_status", "note_summary"), ("notes_status", "used_later_in_book"),
    ("equivalents", "mathlib", "status"),
    ("equivalents", "mathlib", "candidates"),
    ("equivalents", "mathlib", "exact_equivalent"),
    ("equivalents", "repository", "status"),
    ("equivalents", "repository", "candidates"),
    ("equivalents", "repository", "exact_equivalent"),
    ("likely_lean_representation", "sketch"),
    ("likely_lean_representation", "blockers"),
)


def load(path):
    with path.open(encoding="utf-8") as handle:
        value = yaml.safe_load(handle)
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain a top-level mapping")
    return value


def nested(mapping, keys):
    value = mapping
    for key in keys:
        if not isinstance(value, dict) or key not in value:
            return None
        value = value[key]
    return value


def inventory_of(data):
    inventory = data.get("inventory")
    if isinstance(inventory, list):
        if not all(isinstance(entry, dict) for entry in inventory):
            raise ValueError("every inventory entry must be a mapping")
        return inventory
    if "declaration_fields" in data and "declarations" in data:
        raise ValueError("legacy compact declarations are rejected; use the readable schema")
    raise ValueError("missing canonical top-level `inventory` list")


def resolve(descriptor_path, descriptor):
    package = descriptor.get("package")
    if not isinstance(package, dict):
        return descriptor, descriptor
    inv_spec = package.get("declaration_inventory")
    dag_spec = package.get("chapter_local_dependency_dag")
    if not isinstance(inv_spec, dict) or not isinstance(dag_spec, dict):
        raise ValueError("package must specify declaration inventory and DAG components")
    if "file" in inv_spec and "files" in inv_spec:
        raise ValueError("inventory package must use either `file` or `files`, not both")
    names = [inv_spec["file"]] if isinstance(inv_spec.get("file"), str) else inv_spec.get("files")
    if not isinstance(names, list) or not names or not all(isinstance(x, str) and x for x in names):
        raise ValueError("inventory package needs a nonempty `file` or `files` value")
    merged = []
    for name in names:
        path = descriptor_path.parent / name
        if not path.is_file():
            raise ValueError(f"missing inventory component: {path}")
        merged.extend(inventory_of(load(path)))
    expected = inv_spec.get("entry_count")
    if isinstance(expected, int) and expected != len(merged):
        raise ValueError(f"inventory entry_count={expected}, loaded={len(merged)}")
    dag_name = dag_spec.get("file")
    if not isinstance(dag_name, str) or not dag_name:
        raise ValueError("DAG package requires a nonempty `file`")
    dag_path = descriptor_path.parent / dag_name
    if not dag_path.is_file():
        raise ValueError(f"missing DAG component: {dag_path}")
    inventory_data = {"inventory": merged}
    if "completeness_check" in descriptor:
        inventory_data["completeness_check"] = descriptor["completeness_check"]
    return inventory_data, load(dag_path)


def edge_list(dag_data):
    dag = dag_data.get("chapter_local_dependency_dag", dag_data)
    if not isinstance(dag, dict) or not isinstance(dag.get("edges"), list):
        raise ValueError("DAG requires an `edges` list")
    result = []
    for index, edge in enumerate(dag["edges"]):
        if isinstance(edge, dict):
            source, target = edge.get("from"), edge.get("to")
        elif isinstance(edge, list) and len(edge) >= 2:
            source, target = edge[:2]
        else:
            raise ValueError(f"unsupported DAG edge at index {index}")
        if not isinstance(source, str) or not isinstance(target, str):
            raise ValueError(f"DAG edge {index} endpoints must be strings")
        result.append((source, target))
    return result


def cyclic(nodes, edges):
    outgoing = defaultdict(list)
    indegree = {node: 0 for node in nodes}
    for source, target in edges:
        outgoing[source].append(target)
        indegree[target] += 1
    queue = deque(node for node in nodes if indegree[node] == 0)
    seen = 0
    while queue:
        node = queue.popleft()
        seen += 1
        for target in outgoing[node]:
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    return seen != len(nodes)


def validate_entry(chapter, index, entry):
    errors = []
    where = f"chapter {chapter} inventory[{index}]"
    for field in sorted(ENTRY_FIELDS - entry.keys()):
        errors.append(f"{where}: missing `{field}`")
    for path in NESTED_FIELDS:
        if nested(entry, path) is None:
            errors.append(f"{where}: missing `{'.'.join(path)}`")
    if entry.get("pass") not in PASSES:
        errors.append(f"{where}: invalid pass {entry.get('pass')!r}")
    if entry.get("difficulty") not in DIFFICULTIES:
        errors.append(f"{where}: invalid difficulty {entry.get('difficulty')!r}")
    kind = str(entry.get("kind", "")).replace("_", " ").lower()
    if kind == "exercise" and entry.get("pass") != "exercise":
        errors.append(f"{where}: an exercise must use pass `exercise`")
    if kind != "exercise" and entry.get("pass") == "exercise":
        errors.append(f"{where}: a non-exercise may not use pass `exercise`")
    for path in (
        ("equivalents", "mathlib", "exact_equivalent"),
        ("equivalents", "repository", "exact_equivalent"),
    ):
        value = nested(entry, path)
        if value is not None and not isinstance(value, bool):
            errors.append(f"{where}: `{'.'.join(path)}` must be Boolean")
    return errors


def validate_chapter(chapter, path):
    descriptor = load(path)
    inventory_data, dag_data = resolve(path, descriptor)
    inventory = inventory_of(inventory_data)
    errors = []
    for index, entry in enumerate(inventory):
        errors.extend(validate_entry(chapter, index, entry))
    identifiers = [entry.get("id") for entry in inventory if isinstance(entry.get("id"), str)]
    counts = Counter(identifiers)
    duplicates = sorted(identifier for identifier, count in counts.items() if count > 1)
    if duplicates:
        errors.append(f"chapter {chapter}: duplicate identifiers {duplicates}")
    nodes = set(identifiers)
    for entry in inventory:
        for dependency in nested(entry, ("dependencies", "chapter_local")) or []:
            if isinstance(dependency, str) and dependency not in nodes:
                errors.append(f"chapter {chapter} {entry.get('id')}: unresolved dependency {dependency}")
    edges = edge_list(dag_data)
    valid_edges = []
    for source, target in edges:
        if source not in nodes:
            errors.append(f"chapter {chapter} DAG: unknown source {source}")
        if target not in nodes:
            errors.append(f"chapter {chapter} DAG: unknown target {target}")
        if source == target:
            errors.append(f"chapter {chapter} DAG: self-loop {source}")
        if source in nodes and target in nodes and source != target:
            valid_edges.append((source, target))
    if cyclic(nodes, valid_edges):
        errors.append(f"chapter {chapter} DAG: directed cycle detected")
    completeness = inventory_data.get("completeness_check")
    if isinstance(completeness, dict) and completeness.get("missing_numbered_labels"):
        errors.append(
            f"chapter {chapter}: missing numbered labels "
            f"{completeness['missing_numbered_labels']}"
        )
    return errors, len(inventory), len(edges)


def main():
    errors = []
    if not MANIFEST.is_file():
        errors.append(f"missing {MANIFEST.relative_to(ROOT)}")
    else:
        manifest = load(MANIFEST)
        chapters = manifest.get("chapters")
        numbers = {
            item.get("number") for item in chapters or [] if isinstance(item, dict)
        }
        if numbers != set(range(1, 9)):
            errors.append(f"BookManifest chapter numbers must be 1..8, found {sorted(numbers)}")
    entries = edges = 0
    for chapter in range(1, 9):
        path = SPEC / f"Chapter{chapter:02d}.yaml"
        if not path.is_file():
            errors.append(f"chapter {chapter}: missing {path.relative_to(ROOT)}")
            continue
        try:
            chapter_errors, count, edge_count = validate_chapter(chapter, path)
            errors.extend(chapter_errors)
            entries += count
            edges += edge_count
        except (OSError, ValueError, yaml.YAMLError) as exc:
            errors.append(f"chapter {chapter}: {path.relative_to(ROOT)}: {exc}")
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        print(f"FAILED: {len(errors)} error(s); loaded {entries} entries and {edges} DAG edges.")
        return 1
    print(f"PASS: all eight specifications; {entries} entries and {edges} DAG edges.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
