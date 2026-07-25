/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.ElementaryLemmas
import Mathlib.Probability.Moments.SubGaussian

/-!
# Chapter 3: Hoeffding bounds

The moment-generating-function part of Lemma 3.1.1 and the one-sided form of
Theorem 3.1.2 are obtained from Mathlib's proved sub-Gaussian API.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section HoeffdingLemma

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} {a b : ℝ}

/--
The mgf conclusion of Hoeffding's lemma.

Source: Lemma 3.1.1, printed pp. 113–114; specification id `lemma_3_1_1`.
The second-derivative estimate for the cgf remains a separate proof obligation.
-/
theorem hoeffding_mgf
    (hX : AEMeasurable X μ)
    (hbounded : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hcentered : μ[X] = 0) :
    HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) μ :=
  ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    hX hbounded hcentered

/-- The explicit mgf inequality supplied by `hoeffding_mgf`. -/
theorem hoeffding_mgf_le
    (hX : AEMeasurable X μ)
    (hbounded : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hcentered : μ[X] = 0) (t : ℝ) :
    mgf X μ t ≤ Real.exp (((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) * t ^ 2 / 2) :=
  (hoeffding_mgf hX hbounded hcentered).mgf_le t

end HoeffdingLemma

section HoeffdingSum

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} (X : Fin n → Ω → ℝ)
  (a b : Fin n → ℝ)

/--
One-sided Hoeffding inequality for a finite independent centred sum.

Source: Theorem 3.1.2, printed p. 114; specification id `theorem_3_1_2`.
The corresponding lower-tail statement follows by applying this theorem to
`-X`; the two-sided display additionally uses the union bound.
-/
theorem hoeffding_sum_upper_tail
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbounded : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    (hcentered : ∀ i, μ[X i] = 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i, X i ω} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ i, ((((‖b i - a i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)))) := by
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (X i) ((‖b i - a i‖₊ / 2) ^ 2) μ := by
    intro i _hi
    exact hoeffding_mgf (hmeas i) (hbounded i) (hcentered i)
  simpa using
    (ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      hindep hsub hε)

end HoeffdingSum

end Chapter03
end InfiniteDimensionalStatistics
