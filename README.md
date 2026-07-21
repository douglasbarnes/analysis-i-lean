# Analysis I in Lean

A declaration-level formalisation audit of the supplied **Analysis I** lecture notes (W. T. Gowers,
Lent 2015). The source contains **101 theorem-like environments**. This repository does not duplicate
standard Mathlib theorems: each existing result is mapped in [`THEOREM_AUDIT.md`](THEOREM_AUDIT.md),
while course-specific packaging is proved locally.

## Current closure

- 66 declarations map directly to standard Mathlib coverage.
- 31 declarations require a corrected formal statement or Mathlib's standard abstraction.
- 3 declarations duplicate earlier statements in the notes.
- 1 declaration is proved locally in `AnalysisI/Local/Sequences.lean`.
- The machine-readable 101-entry audit is in `AnalysisI/SourceAudit.lean`.
- No `sorry`, `admit`, proof-hiding `axiom`, or proof-hiding `opaque` declaration is permitted.

This initial repository is an **audit-complete baseline**, not a claim that every corrected source
formulation has been re-proved from first principles. Existing Mathlib results are skipped exactly as
requested. The remaining closure work is the set of entries marked `reformulated`, principally the
translation of informal hypotheses and the choice between Darboux/Riemann and Mathlib box/interval
integral APIs.

## Toolchain

- Lean `v4.30.0`
- Mathlib `v4.30.0`

```bash
lake update
lake build
python3 scripts/check_audit.py
```

## Repository layout

- `AnalysisI/SourceAudit.lean` — machine-readable inventory and coverage decision for all 101 declarations.
- `AnalysisI/LibrarySmoke.lean` — representative theorem aliases that exercise the selected Mathlib APIs.
- `AnalysisI/Local/Sequences.lean` — local proof of the one course-specific theorem currently retained.
- `THEOREM_AUDIT.md` — human-readable source-to-Mathlib table.
- `SOURCE_CORRECTIONS.md` — exact corrections needed before formalisation.
- `.github/workflows/lean.yml` — reproducible build and no-placeholder checks.

## Policy

The project treats a theorem as closed only when one of the following holds:

1. its mathematical content is supplied by a named Mathlib declaration or declaration family;
2. a local theorem compiles without `sorry`, `admit`, new axioms, or opaque proof hiding;
3. it is a literal duplicate of an earlier source theorem.

A malformed source statement is never encoded by silently strengthening or weakening it; the correction
is recorded explicitly.
