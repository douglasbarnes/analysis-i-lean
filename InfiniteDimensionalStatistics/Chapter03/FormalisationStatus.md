# Chapter 3 Formalisation Status

Date: 2026-07-26  
Source: Giné–Nickl, *Mathematical Foundations of Infinite-Dimensional Statistical Models*, Chapter 3  
Specification: `InfiniteDimensionalStatistics/Spec/Chapter03.yaml`  
Implementation root: `InfiniteDimensionalStatistics/Chapter03.lean`

## Verification status

This implementation has **not been compiled or checked by Lean** in this work session, at the user's request. No GitHub Actions workflow was created or invoked. All declarations below therefore remain subject to later local elaboration and proof checking.

The implementation contains no intentional `sorry`, `admit`, new axiom, or `opaque` proof substitute. A source theorem is not considered formalised merely because its objects or hypotheses have been represented.

## Implemented object layer

The current modules provide source-order interfaces for:

- empirical measures, empirical means, centred and uncentred empirical processes, kernel estimators and sample boundedness;
- logarithmic moment-generating functions, Rademacher families, Bennett/Bernstein quantities, outer probability and outer expectation;
- independent copies, symmetrisation objects, Rademacher processes, contractions and class hulls;
- covering, packing and bracketing numbers, entropy integrals and entropy-growth conditions;
- Hamming geometry, Lorentz `L_{2,1}`, Talagrand convex distance and product-space coordinate replacement;
- self-bounding variables, bounded differences and entropy-method functionals;
- empirical `L1`/`L2` pseudometrics, local classes and Koltchinskii–Pollard entropy;
- canonical order-two U-statistics and explicit placeholders for the source-defined nonnegative scales `A,B,C,D`;
- VC traces, shattering, VC dimension, VC-subgraph and VC-type classes;
- bounded `p`-variation and translate/dilate classes;
- measurable majorants, measurable covers, outer convergence in probability, outer law and asymptotic tightness;
- Glivenko–Cantelli, pre-Gaussian, Donsker, Gaussian bridge/motion and asymptotic equicontinuity predicates;
- symmetric convex sequential closure and the corrected local class from Theorem 3.7.52.

## Proved or library-backed results

The following results have Lean proof terms in the repository, although they remain uncompiled in this session:

- empirical-measure evaluation, total-mass, Bochner-integration and centred-sum identities;
- Hoeffding's sub-Gaussian mgf conclusion and finite independent-sum upper and two-sided tail bounds, using Mathlib's `HasSubgaussianMGF` API;
- the weighted Rademacher sub-Gaussian and two-sided tail bounds of Example 3.1.3;
- the generic exponential-Markov/Chernoff consequence of a Bennett mgf estimate;
- the log-sum-exp finite maximal inequality underlying Theorem 3.1.10;
- elementary Hamming, coordinate-replacement, entropy-function, product-geometry, local-class and outer-measure lemmas;
- Mathlib-backed finite Sauer–Shelah trace bound and exact VC complement permanence;
- finite-class uniform strong law/Glivenko–Cantelli theorem via Mathlib's Banach-valued strong law;
- measurable bounded-continuous characterization of weak convergence, Portmanteau implications and null-frontier convergence;
- measurable Prokhorov compactness for tight probability-measure families;
- measurable continuous-mapping, convergence-in-probability-to-distribution and Slutsky results.

## Source blockers

The following statements cannot be completed faithfully until their exact source displays are recovered from the rendered book pages:

- Theorem 3.1.9;
- Theorem 3.2.9 and Lemmas 3.2.10–3.2.11;
- equation (3.48);
- Theorem 3.4.1 and the exact definitions of its scale quantities;
- Theorem 3.5.13;
- Theorem 3.5.21;
- Definition 3.7.5 (`P`-perfect maps/classes);
- Proposition 3.7.49, Corollary 3.7.50 and Item 3.7.51;
- apparent source-number gaps 3.3.12, 3.5.14 and 3.5.16–3.5.20.

The uploaded-PDF retrieval service was unavailable during this work session. No blocked formula or constant was reconstructed from memory.

## Major unproved theorem families

Even after the source blockers are resolved, a complete chapter still requires genuine Lean proofs of, among others:

- Bennett and Bernstein mgf inequalities under the book's boundedness and moment hypotheses;
- Levy, Levy–Ottaviani and Hoffmann–Jørgensen maximal/moment inequalities;
- symmetrisation, desymmetrisation, contraction and multiplier inequalities;
- Talagrand convex-distance and entropy-method concentration theorems;
- moment inequalities and canonical U-statistic concentration;
- chaining, Dudley, bracketing and local entropy theorems;
- VC positivity-space, Boolean permanence and polynomial packing estimates beyond the finite Sauer–Shelah core;
- outer Glivenko–Cantelli characterisations for general classes;
- finite-dimensional central limit theory, asymptotic tightness criteria, pre-Gaussian/Donsker equivalences and local Donsker theorems;
- all selected exercises whose results are dependencies of the main text.

## Gate decision

Chapter 3 is **not complete**. The object layer is extensive and several foundational theorems are proved or delegated to exact Mathlib results, but the substantive empirical-process theorem layer and the source-blocked statements remain open. The chapter must not be marked complete until those proofs are present and a later local Lean check succeeds.
