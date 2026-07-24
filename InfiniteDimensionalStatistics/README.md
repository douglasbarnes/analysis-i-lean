# Infinite-Dimensional Statistics formalisation

This directory is the governance and module baseline for a Lean 4 formalisation of
*Mathematical Foundations of Infinite-Dimensional Statistical Models*.

## Scope of this baseline

The baseline establishes source control, naming, imports, dependency direction, notation policy,
manifest schema and a chapter-aligned module tree. It contains no new theorem, lemma, axiom or
book-specific mathematical definition.

A book result may enter Lean only after it has a complete `BookManifest.yaml` entry and its source
statement has been audited against the uploaded book.

## Reproducible toolchain pin

| Component | Repository declaration | Exact revision |
|---|---|---|
| Repository baseline | `main` before this skeleton | `c4199b0d8b9149b501b16d1ab72252264cdc003b` |
| Lean | `leanprover/lean4:v4.30.0` | `d024af099ca4bf2c86f649261ebf59565dc8c622` |
| Lake | bundled with Lean 4.30.0 | `5.0.0-src+d024af0`; source revision `d024af099ca4bf2c86f649261ebf59565dc8c622` |
| mathlib | `v4.30.0` | `c5ea00351c28e24afc9f0f84379aa41082b1188f` |

The mathlib tag is deliberately retained in `lakefile.toml`; the resolved commit above is the audit
pin. Any future toolchain change requires a separate governance commit and a full rebuild.

## Module hierarchy

```text
InfiniteDimensionalStatistics.lean
└── InfiniteDimensionalStatistics/
    ├── Prelude.lean
    ├── Foundations/
    │   ├── MeasureTheory.lean
    │   ├── FunctionalAnalysis.lean
    │   ├── Probability.lean
    │   ├── Gaussian.lean
    │   ├── EmpiricalProcess.lean
    │   ├── FunctionSpaces.lean
    │   └── StatisticalDecision.lean
    ├── Chapter01/NonparametricModels.lean
    ├── Chapter02/GaussianProcesses.lean
    ├── Chapter03/EmpiricalProcesses.lean
    ├── Chapter04/FunctionSpacesAndApproximation.lean
    ├── Chapter05/LinearNonparametricEstimators.lean
    ├── Chapter06/MinimaxParadigm.lean
    ├── Chapter07/LikelihoodProcedures.lean
    └── Chapter08/AdaptiveInference.lean
```

The root is a Lake target and is included in `defaultTargets`, so the complete repository build also
checks this hierarchy.

## Existing-code reuse audit

The audit distinguishes a genuinely reusable theorem or definition from a source-facing placeholder
whose conclusion is merely supplied as a hypothesis.

| Area | Reusable baseline | Assessment |
|---|---|---|
| Probability | `Probability/Core.lean`; Mathlib probability and measure theory | Reuse the Mathlib APIs directly. Repository wrappers for events, probability spaces, independence, Bochner expectation, variance, convergence and elementary inequalities are useful orientation material, but must be statement-audited before import. |
| Measure theory | Mathlib `MeasureTheory`; `Probability/Core.lean` | Strong existing base: measures, probability measures, measurable maps, integration, push-forward, weak convergence and standard convergence theorems. Avoid duplicating these APIs. |
| Functional analysis | Mathlib analysis; `AnalysisII/CoreTheorems.lean`; `LinearAlgebraCourse/*` | Reuse Mathlib for normed spaces, Banach/Hilbert spaces, continuous linear maps, operator norms and Fréchet derivatives. The repository has small verified wrappers for uniform convergence, Banach fixed points and derivative rules. |
| Gaussian analysis | Mathlib `Mathlib/Probability/Distributions/Gaussian/Basic.lean` and related files | Mathlib already defines real Gaussian laws and `ProbabilityTheory.IsGaussian` for measures on Banach spaces, with linear-image and characteristic-function results. `StatisticsCourse/Core.lean` contains only elementary finite-dimensional interfaces and assumption-forwarding statements; it is not a Gaussian-process foundation. |
| Empirical processes | No adequate module in this repository or the pinned Mathlib release | Build a dedicated foundation after the manifest is complete. Do not model empirical-process results as unstructured `Prop` parameters. |
| Sobolev spaces | Mathlib `Mathlib/Analysis/Distribution/Sobolev.lean`; Mathlib functional-space APIs | The pinned release contains Bessel-potential Sobolev spaces for tempered distributions. Audit compatibility with the book's domains, exponents and norm conventions before reuse. |
| Besov spaces | No repository implementation and no identified pinned-Mathlib implementation | New definitions and approximation results will be required after statement and dependency audits. |
| Wavelets | No repository implementation and no identified pinned-Mathlib wavelet basis theory | Expect a new orthonormal-basis, multiresolution and coefficient-space layer. Reuse general Hilbert-space and summability APIs. |
| Statistical decision theory | `StatisticsCourse/Core.lean`; `OptimisationCourse/Core.lean`; Mathlib probability | Reusable vocabulary exists for statistics, bias, MSE, sufficiency, tests, power, Bayes estimators and optimisation, but many course theorems are assumption-forwarding interfaces. Re-prove book results from precise measure-theoretic definitions rather than importing those placeholders as closure results. |

### Reuse acceptance rule

A reused declaration must satisfy all of the following:

1. its fully elaborated Lean statement matches the manifest entry, up to an explicitly documented
   generalisation or definitional equivalence;
2. every required hypothesis and side condition is represented;
3. `#print axioms` contains only accepted foundational axioms and approved classical principles;
4. the declaration is imported from the lowest stable module that provides it;
5. `mathlib_matches` or `dependencies` records the exact declaration name.

## Proof-escape and structure-field audit

At the pinned repository baseline, the existing repository audit rejects source occurrences of
`sorry`, `admit`, line-leading `axiom`, and line-leading `opaque` declarations. The new
`scripts/check_ids_baseline.py` performs the same repository-wide scan, validates this manifest
schema and reports every structure field whose type is proposition-like. The report is intended to
prevent theorem obligations from being hidden inside records and then omitted from theorem audits.

Known reuse-relevant theorem-bearing structure fields include:

- `IAProbability.ClassicalProbability.nonempty`;
- `IAProbability.Partition.measurable`, `.disjoint`, and `.covers`;
- `MarkovChains.HomogeneousMarkovChain.markov` and `.homogeneous`;
- `ComplexAnalysisCourse.Path.continuousOn`;
- `StatisticsCourse.TestingErrors.typeI` and `.typeII`;
- `StatisticsCourse.TestPerformance.power_eq`.

The generated audit output, not this explanatory list, is authoritative for repository-wide
locations and line numbers.

## Local verification

Do not use GitHub Actions as evidence for this project. From a clean checkout, run:

```bash
lake update
lake exe cache get
python3 scripts/check_audit.py
python3 scripts/check_ids_baseline.py
lake build
```

Record the command output, the repository commit and the resolved dependency commits in the commit
or pull-request description. A successful `lake build` is necessary but not sufficient: statement
and proof audits are separate manifest fields.

## Governance files

- `BookManifest.yaml` is the source-to-Lean ledger and closure checklist.
- `DependencyGraph.md` fixes allowed import directions and dependency layers.
- `NotationPolicy.md` fixes notation, naming, namespace and source-provenance conventions.

## Closure standard

A chapter is complete only when every source item in that chapter has a manifest entry, every entry
has `statement_audited: true`, every theorem-level entry has `proof_audited: true`, every declaration
compiles in the chapter import closure, and every nonempty `axioms` list has been explicitly approved.
