/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.EntropyMethod

/-!
# Chapter 3: Empirical and uniform entropy

Definitions from Section 3.5: the empirical `L²` pseudometric, random covering
and packing numbers, and the Koltchinskii–Pollard uniform entropy integral.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section EmpiricalMetric

variable {S : Type*} [MeasurableSpace S]

/--
The empirical `L²` pseudometric
`e_{n,2}(f,g) = (Pₙ (f-g)²)^{1/2}`.

Source: unnumbered definition on p. 184; specification id
`empirical_L2_metric`.
-/
def empiricalL2PseudoMetric {n : ℕ} (X : Fin n → S)
    (f g : S → ℝ) : ℝ :=
  Real.sqrt (empiricalMean X fun x ↦ (f x - g x) ^ 2)

/-- Random covering number in the empirical pseudometric. -/
def empiricalCoveringNumber {n : ℕ} (X : Fin n → S)
    (𝓕 : Set (S → ℝ)) (ε : ℝ) : WithTop ℕ :=
  coveringNumber (empiricalL2PseudoMetric X) 𝓕 ε

/-- Random packing number in the empirical pseudometric. -/
def empiricalPackingNumber {n : ℕ} (X : Fin n → S)
    (𝓕 : Set (S → ℝ)) (ε : ℝ) : WithTop ℕ :=
  packingNumber (empiricalL2PseudoMetric X) 𝓕 ε

/-- Squared empirical radius of a function class. -/
def empiricalSquaredRadius {n : ℕ} (X : Fin n → S)
    (𝓕 : Set (S → ℝ)) : ℝ≥0∞ :=
  ⨆ f : 𝓕, ENNReal.ofReal (empiricalMean X fun x ↦ f.1 x ^ 2)

end EmpiricalMetric

section UniformEntropy

variable {S : Type*} [MeasurableSpace S]

/-- Real `L²(Q)` seminorm. -/
def measureL2Seminorm (Q : Measure S) (f : S → ℝ) : ℝ :=
  Real.sqrt (∫ x, f x ^ 2 ∂Q)

/-- The `L²(Q)` pseudometric on real functions. -/
def measureL2PseudoMetric (Q : Measure S) (f g : S → ℝ) : ℝ :=
  measureL2Seminorm Q (fun x ↦ f x - g x)

/-- A probability measure supported by a finite set. -/
def IsFinitelySupportedProbability (Q : Measure S) : Prop :=
  Q Set.univ = 1 ∧ ∃ s : Finset S, Q (s : Set S) = 1

/-- Entropy integral at a fixed finitely supported measure. -/
def entropyIntegralAtMeasure (𝓕 : Set (S → ℝ)) (F : S → ℝ)
    (Q : Measure S) (δ : ℝ) : ℝ :=
  ∫ τ, Set.indicator (Set.Ioc (0 : ℝ) δ)
    (fun r ↦ Real.sqrt
      (Real.log
        (2 * ((coveringNumber (measureL2PseudoMetric Q) 𝓕
          (r * measureL2Seminorm Q F)).untopD 0 : ℕ)))) τ

/--
Koltchinskii–Pollard uniform entropy integral.

Source: equation (3.169), printed pp. 186–187; specification id
`KP_entropy_integral`.
-/
def koltchinskiiPollardEntropyIntegral
    (𝓕 : Set (S → ℝ)) (F : S → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ Q : Measure S,
    if IsFinitelySupportedProbability Q then
      ENNReal.ofReal (entropyIntegralAtMeasure 𝓕 F Q δ)
    else 0

end UniformEntropy

end Chapter03
end InfiniteDimensionalStatistics
