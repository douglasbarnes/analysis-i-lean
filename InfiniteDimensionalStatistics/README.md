# Infinite-Dimensional Statistics

This directory contains the declaration-level specification and subsequent Lean 4 formalisation of Evarist Giné and Richard Nickl, *Mathematical Foundations of Infinite-Dimensional Statistical Models* (Cambridge University Press, 2016).

## Scope

The project covers Chapters 1–8 in source order. Chapter specifications are stored under `InfiniteDimensionalStatistics/Spec/ChapterNN.yaml`. Specifications contain no Lean proofs. They record the exact source location, mathematical statement, hypotheses, quantifier order, constants, dependencies, exercise delegation, notes usage, equivalence audits, likely Lean representation, difficulty and implementation pass.

## Pass semantics

Pass assignment follows the book, not estimated proof difficulty:

- `core`: every unstarred main-text declaration and operative example required for the source-order formalisation;
- `starred`: material explicitly starred by the book;
- `exercise`: extracted exercise declarations meeting the project selection criteria.

Difficulty is recorded independently as one of `routine`, `substantial`, `major-library` or `research-level`.

## Source fidelity

The printed statement is authoritative. Suspected typographical, measurability or generality defects must not be repaired silently. Each such issue is recorded for central review. Official corrigenda are recorded explicitly and may be represented as corrected variants only when the original statement remains traceable.

## Governance files

- `BookManifest.yaml`: book metadata, chapter scope and specification status;
- `DependencyGraph.md`: book-level and chapter-level dependency policy;
- `NotationPolicy.md`: notation and Lean representation conventions;
- `Spec/Schema.md`: canonical chapter-specification schema;
- `scripts/validate_ids_specs.py`: repository validator for all chapter specifications.

## Lean target

The root module is `InfiniteDimensionalStatistics.lean`; the Lake target is `InfiniteDimensionalStatistics`.

Local validation commands:

```bash
lake build InfiniteDimensionalStatistics
python3 scripts/validate_ids_specs.py
python3 scripts/check_audit.py
```

A clean full-repository build must be recorded before implementation phase P2 begins.
