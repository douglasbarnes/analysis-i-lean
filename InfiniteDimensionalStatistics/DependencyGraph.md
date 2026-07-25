# Book-Level Dependency Graph

This graph is architectural. Declaration-level dependencies remain authoritative in each chapter specification.

```mermaid
graph TD
  C1[Chapter 1: Statistical models]
  C2[Chapter 2: Gaussian processes]
  C3[Chapter 3: Empirical processes]
  C4[Chapter 4: Function spaces]
  C5[Chapter 5: Linear estimators]
  C6[Chapter 6: Minimax theory]
  C7[Chapter 7: Likelihood procedures]
  C8[Chapter 8: Adaptive inference]

  C1 --> C5
  C1 --> C6
  C1 --> C7
  C1 --> C8
  C2 --> C3
  C2 --> C4
  C2 --> C5
  C2 --> C6
  C2 --> C7
  C2 --> C8
  C3 --> C4
  C3 --> C5
  C3 --> C6
  C3 --> C7
  C3 --> C8
  C4 --> C5
  C4 --> C6
  C4 --> C7
  C4 --> C8
  C5 --> C6
  C5 --> C7
  C5 --> C8
  C6 --> C7
  C6 --> C8
  C7 --> C8
```

## Formalisation strata

1. **Measure and experiment interfaces:** dominated models, product laws, Gaussian white noise, sequence experiments, likelihoods and expectations.
2. **Process infrastructure:** Gaussian and empirical processes, entropy, concentration, weak convergence and measurable suprema.
3. **Function-space infrastructure:** Fourier analysis, wavelets, Besov/Sobolev spaces, projections and approximation.
4. **Statistical constructions:** estimators, tests, minimax risks and confidence procedures.
5. **Adaptive and Bayesian results:** posterior contraction, Bernstein–von Mises results, model selection and adaptive confidence sets.

Edges must point from prerequisite to dependent. Cross-chapter references should use stable book labels until Lean declaration names are fixed. No dependency may be introduced merely to match the source proof when a substantially smaller mathlib dependency suffices.
