# Infinite-Dimensional Statistics

This directory contains the declaration specifications and, in later phases, the Lean formalisation of Evarist Giné and Richard Nickl, *Mathematical Foundations of Infinite-Dimensional Statistical Models* (first edition, 2016).

## Phase boundary

P0 establishes project governance, notation, dependency metadata, the Lake target, and the validation interface. P1 records declaration-level chapter specifications. No theorem implementation should begin until all eight chapter specifications pass the validator and the clean local build has been recorded.

The specification phase contains no Lean proofs.

## Layout

- `BookManifest.yaml` — source, chapter ranges, expected specification files, pass semantics, and chapter status.
- `DependencyGraph.md` — book-level dependency architecture.
- `NotationPolicy.md` — binding decisions for notation and source fidelity.
- `Spec/ChapterNN.yaml` — chapter entry point.
- `Spec/SCHEMA.md` — canonical schema and package-loader rules.
- `../InfiniteDimensionalStatistics.lean` — root Lake module.
- `../scripts/validate_infinite_dimensional_statistics_specs.py` — cross-chapter validator.

## Required checks

```bash
python3 -m pip install PyYAML
python3 scripts/validate_infinite_dimensional_statistics_specs.py
lake build InfiniteDimensionalStatistics
python3 scripts/check_audit.py
```

A P1 chapter is not complete merely because a YAML file exists. It must contain precise statements, complete hypotheses and quantifier order, declaration-specific equivalence audits, valid source-pass classification, a valid acyclic dependency DAG, and no unresolved placeholder transcription.
