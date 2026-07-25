# Mathematics Lecture Courses in Lean

A growing Lean 4 formalisation of university mathematics lecture courses and book-length mathematical projects. The repository is organised as a collection of independent libraries rather than around a single analysis sequence.

The current course material is based on Cambridge lecture notes published at https://dec41.user.srcf.net/notes/ and uses Mathlib wherever an existing theorem matches the source statement. Course- or project-specific results are proved locally or represented using explicit hypotheses that preserve the mathematical content of the source.

## Included courses

### Part IA

- Analysis I
- Groups
- Numbers and Sets
- Probability

### Part IB

- Analysis II
- Linear Algebra
- Markov Chains
- Complex Analysis
- Complex Methods
- Geometry
- Groups, Rings and Modules
- Statistics
- Metric and Topological Spaces
- Optimisation

## Book projects

- Infinite-Dimensional Statistics — a source-order formalisation of Giné and Nickl, *Mathematical Foundations of Infinite-Dimensional Statistical Models*.

There are currently **15 Lake library targets**: 14 course libraries and one book-project library. Each target can be built independently, while `lake build` checks the complete collection.

## Formalisation and audit structure

Course and project directories contain the Lean implementation and, where available, source-order inventories and declaration audits. Standard Mathlib declarations are reused rather than duplicated. Source statements that require additional hypotheses are formalised with those hypotheses made explicit instead of being silently strengthened or weakened.

The repository audit rejects:

- `sorry` and `admit` proof placeholders;
- newly declared axioms;
- `opaque` declarations used to hide proofs.

The infinite-dimensional statistics project has additional source-governance files under `InfiniteDimensionalStatistics/` and validates its chapter specifications with:

```bash
python3 scripts/validate_ids_specs.py
```

## Toolchain

- Lean `v4.30.0`
- Mathlib `v4.30.0`

```bash
lake update
lake build
python3 scripts/check_audit.py
```

GitHub Actions runs the same build and audit process for pull requests.
