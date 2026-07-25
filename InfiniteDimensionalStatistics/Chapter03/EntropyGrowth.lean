/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.UStatistics

/-!
# Chapter 3: Entropy growth conditions

Predicates for regular, polynomial, and lower entropy growth from Section 3.5.
Source-sensitive numerical ranges are parameters of the predicates, not silently
chosen constants.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section GrowthFunctions

/-- A nonnegative entropy majorant with a named regularity constant. -/
structure RegularEntropyMajorant where
  H : ℝ → ℝ
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  nonnegative : ∀ x, 0 ≤ H x
  antitone : Antitone H

/-- The square-root entropy primitive associated with `H`. -/
def RegularEntropyMajorant.primitive (h : RegularEntropyMajorant)
    (δ : ℝ) : ℝ :=
  ∫ t, Set.indicator (Set.Ioc (0 : ℝ) δ)
    (fun x ↦ Real.sqrt (h.H x)) t

/-- Scaling condition used in the regular-entropy calculus. -/
def RegularEntropyMajorant.HasScalingControl
    (h : RegularEntropyMajorant) : Prop :=
  ∀ x > 0, h.primitive x ≤ h.constant * x * Real.sqrt (h.H x)

end GrowthFunctions

section UniformEntropyConditions

variable {S : Type*} [MeasurableSpace S]

/-- Uniform entropy is bounded by `H(1/ε)` over finitely supported probabilities. -/
def HasUniformEntropyMajorant
    (𝓕 : Set (S → ℝ)) (F : S → ℝ)
    (H : ℝ → ℝ) : Prop :=
  ∀ Q : Measure S, IsFinitelySupportedProbability Q →
    ∀ ε > 0,
      ((coveringNumber (measureL2PseudoMetric Q) 𝓕
        (ε * measureL2Seminorm Q F)).untopD 0 : ℕ) ≤
        Nat.floor (Real.exp (H (1 / ε)))

/-- Polynomial uniform entropy condition `N(ε) ≤ (A/ε)^v`. -/
def HasPolynomialUniformEntropy
    (𝓕 : Set (S → ℝ)) (F : S → ℝ)
    (A v : ℝ) : Prop :=
  ∀ Q : Measure S, IsFinitelySupportedProbability Q →
    ∀ ε, 0 < ε → ε ≤ 1 →
      ((coveringNumber (measureL2PseudoMetric Q) 𝓕
        (ε * measureL2Seminorm Q F)).untopD 0 : ℕ) ≤
        Nat.floor ((A / ε) ^ v)

/--
Lower entropy growth on a prescribed scale interval.  This is the formal
content of being full for `H` and `P`; the exact interval endpoints from the
source are supplied as parameters.
-/
def IsFullForEntropy
    (𝓕 : Set (S → ℝ)) (P : Measure S)
    (H : ℝ → ℝ) (F : S → ℝ)
    (c εmin εmax : ℝ) : Prop :=
  0 < c ∧ 0 ≤ εmin ∧ εmin ≤ εmax ∧
  ∀ ε, εmin ≤ ε → ε ≤ εmax →
    Real.exp (c * H (measureL2Seminorm P F / ε)) ≤
      ((coveringNumber (measureL2PseudoMetric P) 𝓕 ε).untopD 0 : ℕ)

end UniformEntropyConditions

end Chapter03
end InfiniteDimensionalStatistics
