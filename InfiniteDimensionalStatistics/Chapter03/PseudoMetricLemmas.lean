/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.SampleBoundedPermanence

/-!
# Chapter 3: Empirical and population pseudometric lemmas

Nonnegativity, symmetry and class monotonicity facts for the empirical `L¹`,
empirical `L²`, population `L²`, and Brownian-motion metrics used throughout the
entropy and weak-convergence sections.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section EmpiricalMetrics

variable {S : Type*} [MeasurableSpace S]

/-- The empirical `L²` pseudometric is nonnegative. -/
theorem empiricalL2PseudoMetric_nonneg {n : ℕ}
    (X : Fin n → S) (f g : S → ℝ) :
    0 ≤ empiricalL2PseudoMetric X f g :=
  Real.sqrt_nonneg _

/-- The empirical `L²` pseudometric is symmetric. -/
theorem empiricalL2PseudoMetric_comm {n : ℕ}
    (X : Fin n → S) (f g : S → ℝ) :
    empiricalL2PseudoMetric X f g = empiricalL2PseudoMetric X g f := by
  unfold empiricalL2PseudoMetric empiricalMean
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The empirical `L¹` pseudometric is nonnegative. -/
theorem empiricalL1PseudoMetric_nonneg {n : ℕ}
    (X : Fin n → S) (f g : S → ℝ) :
    0 ≤ empiricalL1PseudoMetric X f g := by
  unfold empiricalL1PseudoMetric empiricalMean
  positivity

/-- The empirical `L¹` pseudometric is symmetric. -/
theorem empiricalL1PseudoMetric_comm {n : ℕ}
    (X : Fin n → S) (f g : S → ℝ) :
    empiricalL1PseudoMetric X f g = empiricalL1PseudoMetric X g f := by
  unfold empiricalL1PseudoMetric empiricalMean
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  exact abs_sub_comm (f (X i)) (g (X i))

/-- Empirical squared radius is monotone in the function class. -/
theorem empiricalSquaredRadius_mono {n : ℕ}
    (X : Fin n → S) {𝓕 𝓖 : Set (S → ℝ)} (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    empiricalSquaredRadius X 𝓕 ≤ empiricalSquaredRadius X 𝓖 := by
  unfold empiricalSquaredRadius
  refine iSup_le fun f => ?_
  exact le_iSup_of_le (⟨f.1, h𝓕𝓖 f.2⟩ : 𝓖) (by rfl)

end EmpiricalMetrics

section PopulationMetrics

variable {S : Type*} [MeasurableSpace S]

/-- The population squared `L²` size is nonnegative. -/
theorem populationSquaredL2_nonneg (P : Measure S) (f : S → ℝ) :
    0 ≤ populationSquaredL2 P f := by
  unfold populationSquaredL2
  exact integral_nonneg fun x => sq_nonneg (f x)

/-- The real `L²(Q)` seminorm is nonnegative. -/
theorem measureL2Seminorm_nonneg (Q : Measure S) (f : S → ℝ) :
    0 ≤ measureL2Seminorm Q f :=
  Real.sqrt_nonneg _

/-- The population `L²` pseudometric is nonnegative. -/
theorem measureL2PseudoMetric_nonneg (Q : Measure S) (f g : S → ℝ) :
    0 ≤ measureL2PseudoMetric Q f g :=
  measureL2Seminorm_nonneg Q _

/-- The population `L²` pseudometric is symmetric. -/
theorem measureL2PseudoMetric_comm (Q : Measure S) (f g : S → ℝ) :
    measureL2PseudoMetric Q f g = measureL2PseudoMetric Q g f := by
  unfold measureL2PseudoMetric measureL2Seminorm
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The Brownian-motion metric is nonnegative. -/
theorem brownianMotionMetric_nonneg (P : Measure S) (f g : S → ℝ) :
    0 ≤ brownianMotionMetric P f g :=
  measureL2PseudoMetric_nonneg P f g

/-- The Brownian-motion metric is symmetric. -/
theorem brownianMotionMetric_comm (P : Measure S) (f g : S → ℝ) :
    brownianMotionMetric P f g = brownianMotionMetric P g f :=
  measureL2PseudoMetric_comm P f g

end PopulationMetrics

end Chapter03
end InfiniteDimensionalStatistics
