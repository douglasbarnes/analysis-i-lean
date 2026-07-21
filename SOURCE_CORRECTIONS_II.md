# Analysis II source corrections

The following corrections are required before the corresponding prose can be encoded as a well-typed Lean statement. They are not silently applied.

## II.3: Uniform convergence and integrals (lines 247–252)

The notes use the Darboux Riemann integral. Mathlib's primary interval integral is Bochner/Lebesgue; the Riemann statement must be expressed through BoxIntegral or derived from continuous integrability.

## II.8: Source theorem 8 (lines 489–499)

The radius naturally takes values in ℝ≥0∞, not a real interval '[0,+∞]'.

## II.9: Termwise differentiation of power series (lines 519–529)

Correct the source typo '(x-n)^n' to '(x-a)^n' and use exponent n-1 in the derived series.

## II.11: Riemann criterion for integrability (lines 679–684)

This is a Darboux upper/lower-sum criterion and should not be conflated with Mathlib's default Bochner integral.

## II.12: Source theorem 12 (lines 687–689)

Requires a precise BoxIntegral/Darboux formulation and subtype domains.

## II.14: Source theorem 14 (lines 746–748)

Requires the BoxIntegral notion of Riemann integrability.

## II.15: Source theorem 15 (lines 782–791)

The coordinatewise Riemann definition is replaced by the Bochner integral, where the norm inequality is standard and more general.

## II.17: Lebesgue's theorem on the Riemann integral* (lines 923–925)

The discontinuity-set criterion requires reconciling Darboux Riemann integrability with Mathlib's measure-theoretic APIs.

## II.19: Source theorem 19 (lines 1173–1179)

Lean permits one canonical Norm instance at a time; comparison is expressed through explicit norm functions or uniform equivalences.

## II.35: Source theorem 35 (lines 1521–1527)

The basis-defined Euclidean norm is implemented by transporting the standard norm along a linear equivalence.

## II.36: Source theorem 36 (lines 1542–1544)

Two simultaneous norm structures must be represented explicitly rather than as competing global instances.

## II.53: Picard-Lindel\"of existence theorem (lines 2220–2238)

Correct the missing quantification over y in the Lipschitz hypothesis and model the closed ball and time interval as sets/subtypes.

## II.56: Source theorem 56 (lines 2724–2731)

The coordinate theorem requires explicit finite index types, standard bases, and partial-derivative definitions.

## II.58: Source theorem 58 (lines 2844–2849)

The two special operator-norm formulae are represented by scalar multiplication and the Riesz isometry.

## II.64: Source theorem 64 (lines 3027–3029)

The source writes f:U→ℝⁿ but the discussion uses general ℝᵐ; formalization uses finite index types and continuous multilinear derivatives.

## II.65: Inverse function theorem (lines 3074–3080)

Correct the codomain from ℝᵐ to ℝⁿ before assuming Df(a) is an invertible endomorphism.

## II.67: Source theorem 67 (lines 3365–3371)

The summation formula needs explicit finite index types, coordinates, and a base point.

## II.68: Second-order Taylor's theorem (lines 3379–3385)

Correct D²f(h,h) to D²f(a)(h,h), require a+h∈U (or h in a small ball), and formulate E(h)=o(‖h‖²) with IsLittleO.

## Definition-level defects

- Line 955 prints the Euclidean norm as `(∑ xᵢ²)²`; it must be `(∑ xᵢ²)^{1/2}`.
- Line 962 ends with `‖x‖² + ‖y‖²` where the intended square is `(‖x‖ + ‖y‖)²`.
- Line 2552 defines the partial derivative using `t → ∞`; it must use `t → 0`.
- The continuity definition around line 2018 uses `f(x)` where the ball must be centered at `f(y)`.
- Several displayed integrals use the wrong dummy variable (`dt` instead of `dx`); the formal statements use consistent binders.
- The inverse function theorem states `f : U → ℝᵐ` but assumes an invertible derivative `ℝⁿ → ℝⁿ`; the codomain must be `ℝⁿ` (or one must assume `m=n` and identify the spaces).
