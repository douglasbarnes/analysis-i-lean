# Infinite-Dimensional Statistics Dependency Graph

This file governs source-order dependencies for the book formalisation. It is not a substitute for the declaration-level DAG stored in each chapter specification.

## Chapter graph

```text
Chapter 1  Nonparametric statistical models
   ├──> Chapter 5  Linear nonparametric estimators
   ├──> Chapter 6  The minimax paradigm
   └──> Chapter 7  Likelihood-based procedures

Chapter 2  Gaussian processes
   ├──> Chapter 3  Empirical processes
   ├──> Chapter 4  Function spaces and approximation theory
   ├──> Chapter 5
   ├──> Chapter 6
   ├──> Chapter 7
   └──> Chapter 8  Adaptive inference

Chapter 3  Empirical processes
   ├──> Chapter 4
   ├──> Chapter 5
   ├──> Chapter 6
   ├──> Chapter 7
   └──> Chapter 8

Chapter 4  Function spaces and approximation theory
   ├──> Chapter 5
   ├──> Chapter 6
   ├──> Chapter 7
   └──> Chapter 8

Chapter 5  Linear nonparametric estimators
   ├──> Chapter 6
   ├──> Chapter 7
   └──> Chapter 8

Chapter 6  The minimax paradigm
   ├──> Chapter 7
   └──> Chapter 8

Chapter 7  Likelihood-based procedures
   └──> Chapter 8
```

The graph records reusable mathematical infrastructure and explicit later use. It does not require every theorem in a predecessor chapter before work may begin on a successor. Declaration-level dependencies determine the actual implementation order.

## Required cross-chapter interfaces

| Interface | Introduced | Principal downstream users |
| --- | --- | --- |
| Statistical models, experiments, estimators, tests and losses | Chapter 1 | Chapters 5–8 |
| Gaussian random variables, processes, concentration, RKHS and Gaussian measures | Chapter 2 | Chapters 3–8 |
| Empirical measures, empirical processes, entropy and concentration inequalities | Chapter 3 | Chapters 4–8 |
| Approximation operators, wavelets, Sobolev/Besov spaces and sequence norms | Chapter 4 | Chapters 5–8 |
| Kernel/projection estimators and weak or multiscale metrics | Chapter 5 | Chapters 6–8 |
| Information distances, minimax lower/upper bounds and confidence-set abstractions | Chapter 6 | Chapters 7–8 |
| Likelihood tests, nonparametric MLEs, posterior contraction and Bernstein–von Mises interfaces | Chapter 7 | Chapter 8 |

## Dependency rules

1. Every chapter specification must have an acyclic local DAG.
2. Each dependency reference must resolve to a local declaration identifier or an explicit external chapter identifier.
3. Forward references are permitted in the specification but must be labelled as later-book dependencies.
4. Exercises used to complete a proof or supply a reusable lemma are first-class DAG nodes.
5. Notes-section results used later are first-class nodes; purely historical notes are not.
6. A theorem may depend on a difficult declaration without moving either declaration to the `starred` pass. Pass assignment follows source typography; difficulty is a separate field.

## Initial implementation strata

1. Measure-theoretic statistical-model interfaces from Chapter 1.
2. Gaussian and empirical-process foundations from Chapters 2–3.
3. Function-space and approximation infrastructure from Chapter 4.
4. Estimation, minimax and likelihood layers from Chapters 5–7.
5. Adaptive procedures from Chapter 8.

The strata are planning guidance only. The validated declaration DAGs remain authoritative.
