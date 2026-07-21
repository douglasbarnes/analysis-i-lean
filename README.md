# Analysis I and II in Lean

A declaration-level formalisation project for the supplied Cambridge **Analysis I** and **Analysis II**
lecture notes. Standard Mathlib results are not duplicated: each source result is mapped to a named
library declaration or declaration family, while corrected course-level wrappers are compiled locally.

## Scope

| Course | Theorem-like source declarations | Mathlib | Reformulated | Duplicates | Local wrappers |
|---|---:|---:|---:|---:|---:|
| Analysis I | 101 | 66 | 31 | 3 | 1 retained course-specific proof |
| Analysis II | 68 | 47 | 18 | 3 | 17 compiled theorem wrappers plus declaration checks |

The Analysis II material covers uniform convergence, function series, compactness, finite-dimensional
normed spaces, metric spaces, Banach's contraction theorem, Picard–Lindelöf, Fréchet differentiation,
the inverse function theorem, mixed partials, and second-order Taylor expansion.

## Toolchain

- Lean `v4.30.0`
- Mathlib `v4.30.0`

```bash
lake update
lake build
python3 scripts/check_audit.py
```

## Repository layout

### Analysis I

- `AnalysisI/SourceAudit.lean` — machine-readable 101-entry inventory.
- `AnalysisI/LibrarySmoke.lean` — representative Mathlib aliases.
- `AnalysisI/Local/Sequences.lean` — retained local sequence proof.
- `THEOREM_AUDIT.md` and `SOURCE_CORRECTIONS.md` — human-readable audit and corrections.

### Analysis II

- `AnalysisII/SourceAudit.lean` — machine-readable 68-entry inventory.
- `AnalysisII/LibraryCoverage.lean` — compile-time checks for the selected Mathlib APIs.
- `AnalysisII/CoreTheorems.lean` — checked source-facing wrappers for central results.
- `THEOREM_AUDIT_II.md` — complete source-to-Mathlib table.
- `SOURCE_CORRECTIONS_II.md` — theorem- and definition-level corrections.

## Verification policy

A source result is treated as closed only if it is supplied by an exact compiled Mathlib target, proved
locally without proof placeholders, or identified as a duplicate of an already checked result. A malformed
source statement is never silently strengthened or weakened.

The CI workflow runs `lake update`, builds both libraries, and rejects `sorry`, `admit`, new axioms, and
proof-hiding `opaque` declarations.
