# Verification

## Automated checks

The repository CI performs:

1. `lake update` against Mathlib `v4.30.0`;
2. `lake build`, with both `AnalysisI` and `AnalysisII` as default targets;
3. `python3 scripts/check_audit.py`;
4. rejection of `sorry`, `admit`, new `axiom` declarations, and proof-hiding `opaque` declarations.

`AnalysisII/LibraryCoverage.lean` contains compile-time declaration checks for the principal APIs used by
the Analysis II audit. `AnalysisII/CoreTheorems.lean` contains source-facing theorem wrappers for uniform
convergence, Heine–Cantor, elementary topology, Banach fixed points, operator norms, and Fréchet calculus.

## Audit invariants

- Analysis I IDs are exactly `1,…,101`.
- Analysis II IDs are exactly `1,…,68`.
- Every theorem-like source environment has a line range, classification, Mathlib target, and correction
  note where required.
