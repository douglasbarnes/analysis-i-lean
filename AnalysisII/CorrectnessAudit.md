# Analysis II correctness audit

## Scope and source pin

This audit compares the Lean library against every theorem-like environment (`thm`, `prop`, `lemma`, and `cor`) in:

- source: `dalcde/cam-notes/IB_M/analysis_ii.tex`;
- pinned source commit: `0c1046b9244d84f65df513b14f22d26c51fd78b5`;
- verified Git blob: `1202516f75cf75afd8cb0cb2f33912a65fb4fcd0`;
- independently scanned theorem-like environments: **68**.

The audit downloads the file from the pinned commit and recomputes its Git blob hash. A changed or substituted source therefore fails before any Lean coverage claim is evaluated.

## Tests performed

The audit uses four independent layers.

### 1. Independent source-inventory verification

`scripts/check_analysis_ii_correctness.py` downloads the pinned TeX file, verifies its Git blob SHA, and independently scans every theorem, proposition, lemma, and corollary environment. It then parses `AnalysisII/SourceAudit.lean` and checks that:

- both independent scans contain exactly 68 entries;
- IDs are exactly `1..68` in source order;
- every environment kind and exact source line range agrees with the pinned TeX;
- source line ranges are ordered and non-overlapping.

This prevents a missing source environment from being concealed merely by omitting it from the Lean inventory.

### 2. Compiled declaration surface

`AnalysisII/CorrectnessAudit.lean` imports and `#check`s every current course-facing declaration whose name begins `AnalysisII.sourceNNN_`. It is imported by the `AnalysisII` library target. Thus missing, renamed, or ill-typed mapped declarations fail `lake build`.

The current library contains **18 source-linked declarations**, covering **13 explicit source IDs**. Source result 49 intentionally reuses the more general source-10 Heine--Cantor declaration, giving 14 source results with an identifiable target.

### 3. Proof-escape scan

The strict script rejects, within the Analysis II library:

- `sorry`;
- `admit`;
- newly declared `axiom`;
- proof-hiding `opaque` declarations.

This prevents a declaration from satisfying the structural audit while concealing an unfinished proof.

### 4. Statement-fidelity review

Each identifiable declaration was compared manually with the pinned TeX statement. A source result is classified as:

- **full**: the Lean theorem proves the complete source statement, or a genuine generalisation from which the complete statement follows directly;
- **partial**: a declaration exists, but it omits a clause or direction, or assumes a materially stronger hypothesis;
- **unmapped**: no declaration with a verifiable source link exists.

A bare `#check` of an unrelated Mathlib theorem is not accepted as source coverage. Exact Mathlib reuse must identify the source result and expose a compiled theorem or alias with the intended statement.

## Current result

| Classification | Count |
|---|---:|
| Fully verified | **7** |
| Partially formalised | **7** |
| No verifiable declaration target | **54** |
| Total | **68** |

The current Analysis II library therefore **does not pass the strict correctness criterion**.

## Fully verified results

| Source ID | Result | Audit conclusion |
|---:|---|---|
| 10 | Heine--Cantor on a closed bounded interval | `source010_heineCantor` proves the more general compact-set theorem. |
| 28 | Metric balls are open | Faithful general metric-space formulation. |
| 39 | Uniqueness of limits | Faithful generalisation to Hausdorff spaces. |
| 44 | Singletons and finite subsets are closed | Faithful generalisation to `T1Space`. |
| 49 | Heine--Cantor on compact metric spaces | Covered by `source010_heineCantor`. |
| 54 | Uniqueness of the Fréchet derivative | Faithful general normed-space formulation. |
| 59 | Fréchet chain rule | Faithful general normed-space formulation. |

## Partially formalised results

| Source ID | Defect |
|---:|---|
| 1 | The forward implication, uniform convergence implies uniformly Cauchy, is present. The reverse declaration assumes a prescribed pointwise limit instead of deriving existence of the real-valued limit from uniform Cauchyness. It therefore does not prove the source equivalence. |
| 2 | The Lean theorem assumes every function is globally continuous and proves global continuity. The source theorem is local: continuity of every `f_n` at one point of a subset implies continuity of the limit at that point. The global result does not directly instantiate to the source's subtype/local-continuity statement without additional work. |
| 41 | Arbitrary unions and binary intersections of open sets are present. The source also states general finite intersections and that `∅` and the whole space are open. |
| 43 | Arbitrary intersections and binary unions of closed sets are present. The source also states general finite unions and that `∅` and the whole space are closed. |
| 52 | The direct contraction case proves a unique fixed point. The contracting-iterate declaration proves that one constructed point is fixed by `f`, but does not package or prove uniqueness for `f`, which is part of the source theorem. |
| 55 | Only clauses (i), differentiability implies continuity, and (iv), a continuous linear map is its own derivative, are present from the source's seven-clause proposition. |
| 57 | Only clause (iv), `‖A x‖ ≤ ‖A‖ ‖x‖`, is present from the source's five-clause operator-norm proposition. |

## Results without a verifiable declaration target

The following source IDs have no source-linked Lean theorem or exact alias that can be checked for statement fidelity:

`3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 42, 45, 46, 47, 48, 50, 51, 53, 56, 58, 60, 61, 62, 63, 64, 65, 66, 67, 68`.

This includes major results such as uniform convergence and integration, the Weierstrass M-test, power-series differentiation, Riemann-integrability results, Bolzano--Weierstrass in finite dimensions, completeness results, compactness results, finite-dimensional norm equivalence, Picard--Lindelöf, the inverse function theorem, continuous partial derivatives implying differentiability, Taylor's theorem, the mean-value inequality, and zero derivative implying constancy.

## Why the previous audit was insufficient

`AnalysisII/SourceAudit.lean` records source locations and labels them `mathlib`, `reformulated`, or `duplicate`, but it does not store a declaration name or compile a proof witness for each entry. `AnalysisII/LibraryCoverage.lean` contains 20 unlabelled Mathlib `#check` commands. These checks prove that those APIs exist; they do not establish that each of the 68 source statements has been formalised.

Consequently, the previous global build and placeholder audit could pass while most Analysis II results had no inspectable theorem target.

## Reproduction

Run the current-state diagnostic:

```bash
python3 scripts/check_analysis_ii_correctness.py --baseline
```

This downloads and verifies the source, checks the exact 68-entry inventory, and succeeds only when it reproduces the reviewed result `7 full / 7 partial / 54 unmapped` and the current source-linked declaration-ID set.

Run the actual acceptance test:

```bash
python3 scripts/check_analysis_ii_correctness.py --strict
```

This currently exits non-zero. It will pass only when all 68 source results are classified as fully formalised and the reviewed map is updated accordingly.

A local source copy can be supplied without weakening the hash check:

```bash
python3 scripts/check_analysis_ii_correctness.py --baseline --source-file analysis_ii.tex
```

## Required closure standard

For each of the 68 source entries, closure requires:

1. a stable source ID and exact pinned source line range;
2. a named Lean theorem, or an explicit exact alias to a Mathlib theorem;
3. a compiled witness imported by the `AnalysisII` Lake target;
4. a statement-fidelity review covering every clause and both directions of equivalences;
5. no proof placeholders or newly introduced axioms;
6. a passing strict audit and full `lake build`.

Until those conditions hold for every entry, the repository must not describe Analysis II as completely formalised.
