# Part IA — Probability: source audit

Source: [probability.tex](https://dec41.user.srcf.net/notes/IA_L/probability.tex)

Status: **audited, not yet formalised**. The source has 96 non-example declaration environments: 43 definitions/notations, 45 theorem/proposition/corollary declarations, and 8 bundled or duplicate occurrences.

## Planned Lean hierarchy

```text
CambridgeNotes/PartIA/Probability/
  Foundations.lean
  Counting.lean
  Discrete/Basic.lean
  Discrete/Distributions.lean
  Conditional.lean
  Expectation.lean
  Independence.lean
  Inequalities.lean
  GeneratingFunctions.lean
  Branching.lean
  RandomWalk.lean
  Continuous/Basic.lean
  Continuous/Joint.lean
  Continuous/Transform.lean
  Continuous/Distributions.lean
  LimitTheorems.lean
```

## Coverage

Mathlib provides the foundation: measurable spaces, measures, `IsProbabilityMeasure`, pushforward laws, integrals, `PMF`, a.e. equality, and independence. The early modules will package finite/countable probability, conditional probability, expectation, variance, elementary distributions, and inequalities as source-facing proved results. Generating functions, branching processes, Gaussian/Gamma/Beta calculations, SLLN, CLT, and MGF continuity are separate dependency programmes.

## Source corrections required

- Probability-mass functions need non-negativity and total mass one.
- Multinomial identities need the condition `∑ nᵢ = n`.
- Conditional probabilities require positive denominators.
- Random variables must be measurable; statements about sets must say measurable sets.
- Moment, variance, covariance, Cauchy--Schwarz, Markov, Chebyshev, and conditional-expectation statements need their standard integrability assumptions.
- Correlation is undefined at zero variance.
- The branching extinction claim fails for deterministic one-child offspring.
- Density transformation statements require appropriate support and diffeomorphism hypotheses.
- The normal-closure proof has missing notation and an exponent typo.
- The CLT and MGF-continuity statements are sketches and need precise quantified forms and complete proofs.

## Closure policy

A repeated source result is represented by one canonical Lean declaration with references to every source occurrence. Every new declaration must be a checked Mathlib wrapper or a full local proof: no `sorry`, axiom, or opaque proof hiding.
