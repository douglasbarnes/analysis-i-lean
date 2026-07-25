# Mathematics Lecture Courses in Lean

A growing Lean 4 formalisation of university mathematics lecture courses. The repository is organised as a collection of independent course libraries rather than around a single analysis sequence.

The current material is based on Cambridge lecture notes published at https://dec41.user.srcf.net/notes/ and uses Mathlib wherever an existing theorem matches the source statement. Course-specific results are proved locally or represented using explicit hypotheses that preserve the mathematical content of the source.

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

### Book formalisation projects

- Infinite-Dimensional Statistics — Giné and Nickl, currently in the governance and declaration-specification phases.

There are currently **15 Lake libraries**. Each course or book project is exposed as a separate Lake target, so individual libraries can be built independently while `lake build` checks the complete collection.

## Formalisation and audit structure

Course directories contain the Lean implementation and, where available, source-order inventories and declaration audits. Standard Mathlib declarations are reused rather than duplicated. Source statements that require additional hypotheses are formalised with those hypotheses made explicit instead of being silently strengthened or weakened.

The repository audit rejects:

- `sorry` and `admit` proof placeholders;
- newly declared axioms;
- `opaque` declarations used to hide proofs.

The Infinite-Dimensional Statistics specifications have an additional cross-chapter validator:

```bash
python3 -m pip install -r scripts/requirements-spec.txt
python3 scripts/validate_infinite_dimensional_statistics_specs.py
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
