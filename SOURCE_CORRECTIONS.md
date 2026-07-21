# Source corrections

The following source declarations cannot be translated literally into Lean without either adding hypotheses, correcting notation, or choosing Mathlib’s standard abstraction. These changes are semantic, not merely syntactic.

## 7. Theorem 7

**Source:** lines 214–216

Mathlib states this with filter boundedness or asymptotic notation rather than the notes’ sequence predicate.

## 8. Theorem 8

**Source:** lines 222–224

Formalised through `range of a convergent sequence is bounded` in `Mathlib.Topology.MetricSpace.Bounded`.

## 11. Theorem 11

**Source:** lines 260–262

Corrected conclusion: aₙ / bₙ → a / b. The source prints equality and must assume the denominator sequence is eventually nonzero (pointwise nonzero is stronger).

## 15. Theorem 15

**Source:** lines 349–351

Mathlib encodes the property as a typeclass, not as the notes’ custom monotone-sequences axiom.

## 16. Theorem 16

**Source:** lines 361–363

Mathlib encodes least-upper-bound completeness structurally.

## 22. Theorem 22

**Source:** lines 452–454

Formalised through `CauchySeq.tendsto_of_subseq_tendsto` in `Mathlib.Topology.UniformSpace.Cauchy`.

## 24. Theorem 24

**Source:** lines 484–486

The library uses order/completeness typeclasses rather than this implication as a standalone predicate theorem.

## 25. Theorem 25

**Source:** lines 550–556

The source must assume boundedness (or use an extended codomain); otherwise its real-valued limsup/liminf expressions need not exist.

## 28. Comparison test

**Source:** lines 647–649

The eventual multiplicative bound is handled after discarding a finite prefix.

## 31. Theorem 31

**Source:** lines 756–758

Formalised through `real unconditional convergence ⇒ absolute convergence / rearrangement theorem family` in `Mathlib.Analysis.SpecificLimits.Normed`.

## 34. Ratio test

**Source:** lines 838–857

Each displayed quotient requires aₙ ≠ 0. The robust Mathlib form bounds ‖aₙ₊₁‖ directly by c‖aₙ‖, eventually, with 0 ≤ c < 1.

## 35. Condensation test

**Source:** lines 878–883

“< ∞” is replaced by Summable.

## 36. Integral test

**Source:** lines 907–909

The domain is Ici 1 (or ℝ with assumptions on Ici 1), not the malformed interval [1,∞]. The integral is a precise improper/interval integral.

## 50. Theorem 50

**Source:** lines 1281–1283

The quotient branch must require m ≠ 0 and eventual nonvanishing follows locally; “g does not vanish” is ambiguous and stronger than needed.

## 51. Theorem 51

**Source:** lines 1311–1315

This is an equivalent formulation/notation, not a standalone proposition as printed.

## 52. Theorem 52

**Source:** lines 1323–1325

The derivative value must be a separate λ; using f'(x) in the hypothesis presupposes differentiability.

## 57. Theorem 57

**Source:** lines 1426–1430

Formalise f as an ambient map ℝ → ℝ with ContinuousOn/DifferentiableOn hypotheses; the printed subtype-valued map and ambient derivative notation are incompatible.

## 61. Higher-order Rolle's theorem

**Source:** lines 1551–1557

Require n ≥ 1. The notes’ proof incorrectly calls n = 0 the Rolle base case.

## 62. Theorem 62

**Source:** lines 1567–1569

Both functions must be n-times differentiable, not merely differentiable once.

## 63. Taylor's theorem with the Lagrange form of remainder

**Source:** lines 1620–1625

For h < 0 the witness lies in the open segment between a and a+h, not literally Ioo a (a+h). Include n ≥ 1 and precise iterated-derivative hypotheses.

## 65. Theorem 65

**Source:** lines 1753–1759

Use ℝ≥0∞ (or explicit zero/infinite conventions) for radius and limsup; the printed reciprocal formula omits edge cases.

## 72. Theorem 72

**Source:** lines 1963–1968

Require n ≥ 2 and replace the ellipsis by an explicit Finset sum. The geometric factorisation is already in Mathlib.

## 79. Theorem 79

**Source:** lines 2136–2141

The source lower-sum subscript has a typo. Mathlib uses box prepartitions and tagged sums rather than reproducing this exact handwritten Darboux API.

## 80. Theorem 80

**Source:** lines 2188–2193

Formalised through `common refinement (infimum) and upper/lower comparison` in `Mathlib.Analysis.BoxIntegral.Partition.Basic`.

## 81. Riemann's integrability criterion

**Source:** lines 2274–2281

A literal Darboux proof also needs boundedness so all upper/lower sums are finite. Mathlib’s standard box-integral criterion is used instead.

## 91. Theorem 91

**Source:** lines 2552–2554

The source proof only writes the increasing, nonconstant case; decreasing and constant cases need separate handling.

## 94. Theorem 94

**Source:** lines 2640–2649

Index by positive n (or n+1); n = 0 does not define the displayed dissection.

## 95. Fundamental theorem of calculus, part 1

**Source:** lines 2694–2700

At interval endpoints the correct notion is HasDerivWithinAt/one-sided derivative; unrestricted differentiability at every endpoint is not justified.

## 98. Integration by parts

**Source:** lines 2769–2774

Replace “such that everything below exists” by explicit derivative, continuity and integrability hypotheses.

## 99. Taylor's theorem with the integral form of the remainder

**Source:** lines 2785–2791

Use iterated Fréchet derivatives or iteratedDeriv with explicit regularity; the notes also have an index typo in the integration-by-parts induction display.

## 100. Integration by substitution

**Source:** lines 2821–2826

The image/domain and continuity hypotheses are stated explicitly in the library theorem.
