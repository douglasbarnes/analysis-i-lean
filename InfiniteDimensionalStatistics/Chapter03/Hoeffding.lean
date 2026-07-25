/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.ElementaryLemmas
import Mathlib.Probability.Moments.SubGaussian

/-!
# Chapter 3: Hoeffding bounds

The moment-generating-function part of Lemma 3.1.1 and the finite-sum forms of
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

private theorem hoeffding_sum_subgaussian
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbounded : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    (hcentered : ∀ i, μ[X i] = 0) :
    HasSubgaussianMGF (fun ω ↦ ∑ i, X i ω)
      (∑ i, ((‖b i - a i‖₊ / 2) ^ 2 : ℝ≥0)) μ := by
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (X i) ((‖b i - a i‖₊ / 2) ^ 2) μ := by
    intro i _hi
    exact hoeffding_mgf (hmeas i) (hbounded i) (hcentered i)
  simpa using
    (ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun hindep hsub)

/--
One-sided Hoeffding inequality for a finite independent centred sum.

Source: Theorem 3.1.2, printed p. 114; specification id `theorem_3_1_2`.
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
  exact (hoeffding_sum_subgaussian X a b hindep hmeas hbounded hcentered).measure_ge_le hε

/--
Two-sided Hoeffding inequality written as the union of the upper and lower tail
events.  This is the union-bound form immediately preceding the absolute-value
notation in Theorem 3.1.2.
-/
theorem hoeffding_sum_two_sided_union
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbounded : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    (hcentered : ∀ i, μ[X i] = 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real
        ({ω | ε ≤ ∑ i, X i ω} ∪ {ω | ∑ i, X i ω ≤ -ε}) ≤
      2 * Real.exp
        (-ε ^ 2 /
          (2 * ∑ i, ((((‖b i - a i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)))) := by
  let c : ℝ≥0 := ∑ i, ((‖b i - a i‖₊ / 2) ^ 2 : ℝ≥0)
  let S : Ω → ℝ := fun ω ↦ ∑ i, X i ω
  have hS : HasSubgaussianMGF S c μ := by
    simpa [S, c] using hoeffding_sum_subgaussian X a b hindep hmeas hbounded hcentered
  have hupper : μ.real {ω | ε ≤ S ω} ≤ Real.exp (-ε ^ 2 / (2 * c)) :=
    hS.measure_ge_le hε
  have hlower : μ.real {ω | S ω ≤ -ε} ≤ Real.exp (-ε ^ 2 / (2 * c)) := by
    have hneg := hS.neg.measure_ge_le hε
    simpa [S] using hneg
  calc
    μ.real ({ω | ε ≤ ∑ i, X i ω} ∪ {ω | ∑ i, X i ω ≤ -ε})
        ≤ μ.real {ω | ε ≤ S ω} + μ.real {ω | S ω ≤ -ε} := by
          simpa [S] using
            (measureReal_union_le
              (μ := μ) {ω | ε ≤ S ω} {ω | S ω ≤ -ε})
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) + Real.exp (-ε ^ 2 / (2 * c)) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp
        (-ε ^ 2 /
          (2 * ∑ i, ((((‖b i - a i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)))) := by
      simp [c, two_mul]

end HoeffdingSum

end Chapter03
end InfiniteDimensionalStatistics
