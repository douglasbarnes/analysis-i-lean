# Cambridge Part IA and Part IB in Lean

A declaration-level Lean formalisation of every labelled definition, notation, law, lemma,
proposition, theorem, and corollary in the Part IA and Part IB TeX lecture notes published at
https://dec41.user.srcf.net/notes/.

## Coverage

| Part | Courses | Labelled source environments |
|---|---:|---:|
| IA | 8 | 913 |
| IB | 16 | 1,111 |
| **Total** | **24** | **2,024** |

Each course has an ordered, source-line-aware inventory and a declaration audit with one compiled
witness per source environment. Standard Mathlib results are reused where they match exactly;
course-specific statements are proved locally or represented with explicit hypotheses matching the
mathematical certificates required by the source.

## Courses

Part IA: Analysis I; Differential Equations; Dynamics and Relativity; Groups; Numbers and Sets;
Probability; Vector Calculus; Vectors and Matrices.

Part IB: Analysis II; Linear Algebra; Markov Chains; Methods; Quantum Mechanics; Complex Analysis;
Complex Methods; Electromagnetism; Fluid Dynamics; Geometry; Groups, Rings and Modules; Numerical
Analysis; Statistics; Metric and Topological Spaces; Optimisation; Variational Principles.

## Toolchain and verification

- Lean `v4.30.0`
- Mathlib `v4.30.0`

```bash
lake update
lake build
python3 scripts/check_audit.py
```

The CI workflow builds all 24 libraries and rejects proof placeholders, new axioms, and proof-hiding
opaque declarations. A source result is treated as closed only when it is an exact compiled Mathlib
target, has a complete local proof, or is recorded as a duplicate of an already checked result.
Malformed source statements are documented and are never silently strengthened or weakened.
