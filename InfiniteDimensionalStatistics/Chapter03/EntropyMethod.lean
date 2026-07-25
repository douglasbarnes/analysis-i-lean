/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.ProductGeometry

/-!
# Chapter 3: Entropy-method definitions

Coordinate replacement, coordinate deletion, entropy, self-bounding variables,
and bounded differences from Section 3.3.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Coordinates

variable {S : Type*} {n : ℕ}

/-- Replace coordinate `k` of `x` by `y`. -/
def replaceCoordinate (x : Fin n → S) (k : Fin n) (y : S) : Fin n → S :=
  Function.update x k y

/-- Two product points agree away from coordinate `k`. -/
def AgreeOff (k : Fin n) (x y : Fin n → S) : Prop :=
  ∀ i, i ≠ k → x i = y i

/-- A statistic ignores coordinate `k`. -/
def IgnoresCoordinate (Z : (Fin n → S) → ℝ) (k : Fin n) : Prop :=
  ∀ x y, AgreeOff k x y → Z x = Z y

/-- Coordinatewise oscillation of a statistic at `x`. -/
def coordinateOscillation (Z : (Fin n → S) → ℝ)
    (k : Fin n) (x : Fin n → S) : ℝ≥0∞ :=
  ⨆ y : S, ENNReal.ofReal |Z x - Z (replaceCoordinate x k y)|

/-- One-sided coordinate decrement. -/
def coordinateDecrement (Z : (Fin n → S) → ℝ)
    (Zdelete : Fin n → (Fin n → S) → ℝ)
    (k : Fin n) (x : Fin n → S) : ℝ :=
  Z x - Zdelete k x

/--
The self-bounding/subadditive condition of Definition 3.3.2.

Source: Definition 3.3.2, printed p. 151; specification id
`definition_3_3_2`.
-/
def IsSelfBounding (Z : (Fin n → S) → ℝ)
    (Zdelete : Fin n → (Fin n → S) → ℝ) : Prop :=
  (∀ k, IgnoresCoordinate (Zdelete k) k) ∧
  (∀ k x, 0 ≤ coordinateDecrement Z Zdelete k x) ∧
  (∀ k x, coordinateDecrement Z Zdelete k x ≤ 1) ∧
  ∀ x, ∑ k, coordinateDecrement Z Zdelete k x ≤ Z x

/--
The bounded-differences property from Section 3.3.

Source: unnumbered definition before Example 3.3.13, printed p. 161;
specification id `bounded_differences`.
-/
def HasBoundedDifferences (Z : (Fin n → S) → ℝ)
    (c : Fin n → ℝ) : Prop :=
  (∀ k, 0 ≤ c k) ∧
  ∀ k x y, AgreeOff k x y → |Z x - Z y| ≤ c k

/-- Sum of squared bounded-difference constants. -/
def boundedDifferencesVarianceProxy (c : Fin n → ℝ) : ℝ :=
  ∑ k, c k ^ 2

end Coordinates

section Entropy

variable {Ω : Type*} [MeasurableSpace Ω]

/--
Entropy of a nonnegative real random variable:
`Ent(Z) = E[Z log Z] - E[Z] log E[Z]`.
-/
def entropyFunctional (P : Measure Ω) (Z : Ω → ℝ) : ℝ :=
  (∫ ω, Z ω * Real.log (Z ω) ∂P) -
    (∫ ω, Z ω ∂P) * Real.log (∫ ω, Z ω ∂P)

/-- Conditional-coordinate entropy supplied by a coordinate integration operator. -/
def coordinateEntropy
    (Ek : (Ω → ℝ) → Ω → ℝ) (Z : Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ Ek (fun u ↦ Z u * Real.log (Z u)) ω -
    Ek Z ω * Real.log (Ek Z ω)

/-- Log-Laplace transform of a real random variable. -/
def logLaplaceTransform (P : Measure Ω) (Z : Ω → ℝ) (λ : ℝ) : ℝ :=
  Real.log (∫ ω, Real.exp (λ * Z ω) ∂P)

/-- Centred log-Laplace transform. -/
def centredLogLaplaceTransform (P : Measure Ω) (Z : Ω → ℝ) (λ : ℝ) : ℝ :=
  logLaplaceTransform P (fun ω ↦ Z ω - ∫ u, Z u ∂P) λ

/-- The first auxiliary entropy-method function from equation (3.74). -/
def entropyPhi (x : ℝ) : ℝ :=
  Real.exp (-x) - 1 + x

end Entropy

end Chapter03
end InfiniteDimensionalStatistics
