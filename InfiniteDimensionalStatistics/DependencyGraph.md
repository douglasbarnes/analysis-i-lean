# Dependency graph and import policy

This file fixes the import DAG for `InfiniteDimensionalStatistics`. Import direction is a governance
constraint, not a suggestion.

## Layered graph

```text
Mathlib
  │
  ▼
Prelude
  ├───────────────┐
  ▼               ▼
MeasureTheory   FunctionalAnalysis
  │               │
  ▼               │
Probability ◄─────┘
  ├──────────┬───────────────┐
  ▼          ▼               ▼
Gaussian   EmpiricalProcess  StatisticalDecision
  ▲          ▲
  │          │
  └────┐  ┌──┘
       ▼  ▼
    Chapters 1–4
         │
         ▼
    Chapters 5–8
         │
         ▼
InfiniteDimensionalStatistics.lean
```

`FunctionSpaces` depends only on `MeasureTheory` and `FunctionalAnalysis`; it feeds Chapters 4–8.

## Chapter dependencies

| Module | May import |
|---|---|
| Chapter 1 | probability and statistical-decision foundations |
| Chapter 2 | Gaussian, probability and functional-analysis foundations |
| Chapter 3 | empirical-process and Gaussian foundations |
| Chapter 4 | function-space foundations |
| Chapter 5 | Chapters 1 and 4 plus lower foundations |
| Chapter 6 | Chapters 3, 4 and 5 plus lower foundations |
| Chapter 7 | Chapters 1, 3 and 6 plus lower foundations |
| Chapter 8 | Chapters 6 and 7 plus lower foundations |
| Root | chapter aggregators only |

## Mandatory import rules

1. `Prelude.lean` imports Mathlib and declares no mathematics or notation.
2. Foundation modules may import Mathlib through `Prelude` and lower foundation layers only.
3. A chapter may import earlier chapters only when the book-level dependency is recorded in the
   manifest. It may never import a later chapter.
4. Definitions needed by multiple chapters move to the narrowest semantically appropriate
   foundation module. Do not create a generic `Common.lean` dumping ground.
5. Existing course libraries are not imported wholesale into foundations. Reusable declarations
   are either imported from Mathlib directly or exposed through a small, statement-audited bridge
   module added in a later governance commit.
6. Source-audit, declaration-audit and executable-check modules sit above mathematical modules and
   are never imported by them.
7. The root module contains imports only. It must not become an implementation file.
8. Circular imports, upward imports and chapter-to-audit imports are prohibited.

## Declaration-level dependency recording

Every theorem-level manifest entry records dependencies in proof-use order:

1. foundational types and definitions;
2. previously proved book results by manifest ID;
3. exact Mathlib declaration names;
4. local helper lemmas.

A dependency is not closed merely because a file imports a module. The exact declaration used must
be named in `dependencies` or `mathlib_matches`.

## Planned dependency clusters

The following clusters are architectural placeholders, not claims of completed mathematics:

- measure and probability kernels;
- Banach/Hilbert duality and Gaussian measures;
- random and empirical measures;
- symmetrisation, concentration, entropy and chaining;
- Sobolev, Besov, Hölder and sequence spaces;
- approximation operators and wavelet coordinates;
- experiments, losses, tests, estimators and risks;
- minimax lower and upper bounds;
- likelihood, posterior and adaptive procedures.

Each cluster must acquire a manifest-backed declaration graph before implementation begins.
