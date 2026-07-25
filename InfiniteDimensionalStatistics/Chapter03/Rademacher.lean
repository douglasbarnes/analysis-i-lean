/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.Hoeffding

/-!
# Chapter 3: Rademacher sums

The finite weighted Rademacher tail bound of Example 3.1.3, derived from the
proved Hoeffding interface.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section RademacherSums

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ}

/-- A deterministic multiple of a Rademacher variable is centred. -/
theorem integral_mul_rademacher_eq_zero
    (ε : Ω → ℝ) (a : ℝ) (hε : IsRademacher μ ε) :
    (∫ ω, a * ε ω ∂μ) = 0 := by
  rw [integral_const_mul, hε.2.2.2.2, mul_zero]

/-- A Rademacher variable lies in `[-1,1]` almost surely. -/
theorem rademacher_mem_Icc
    (ε : Ω → ℝ) (hε : IsRademacher μ ε) :
    ∀ᵐ ω ∂μ, ε ω ∈ Set.Icc (-1 : ℝ) 1 := by
  filter_upwards [hε.2.1] with ω hω
  rcases hω with hneg | hpos <;> simp [hneg, hpos]

/-- A Rademacher variable is one-sub-Gaussian. -/
theorem rademacher_hasSubgaussianMGF
    (ε : Ω → ℝ) (hε : IsRademacher μ ε) :
    HasSubgaussianMGF ε 1 μ := by
  simpa using
    (hoeffding_mgf hε.1.aemeasurable (rademacher_mem_Icc ε hε) hε.2.2.2.2)

/-- A deterministic multiple of a Rademacher variable lies in `[-|a|, |a|]`. -/
theorem mul_rademacher_mem_Icc
    (ε : Ω → ℝ) (a : ℝ) (hε : IsRademacher μ ε) :
    ∀ᵐ ω ∂μ, a * ε ω ∈ Set.Icc (-|a|) |a| := by
  filter_upwards [hε.2.1] with ω hω
  rcases hω with hneg | hpos
  · rw [hneg]
    constructor <;> simp
  · rw [hpos]
    constructor <;> simp

/-- A deterministic multiple of a Rademacher variable has proxy `a²`. -/
theorem mul_rademacher_hasSubgaussianMGF
    (ε : Ω → ℝ) (a : ℝ) (hε : IsRademacher μ ε) :
    HasSubgaussianMGF (fun ω ↦ a * ε ω) ⟨a ^ 2, sq_nonneg a⟩ μ := by
  simpa using (rademacher_hasSubgaussianMGF ε hε).const_mul a

/-- A weighted independent Rademacher sum has proxy `∑ᵢ aᵢ²`. -/
theorem rademacher_weighted_sum_hasSubgaussianMGF
    (ε : Fin n → Ω → ℝ) (a : Fin n → ℝ)
    (hε : IsRademacherFamily μ ε) :
    HasSubgaussianMGF (rademacherWeightedSum ε a)
      (∑ i, (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)) μ := by
  let Y : Fin n → Ω → ℝ := fun i ω ↦ a i * ε i ω
  have hindep : ProbabilityTheory.iIndepFun Y μ := by
    have h := hε.2.comp (fun i x ↦ a i * x) (fun _ ↦ by fun_prop)
    simpa [Y, Function.comp_def] using h
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (Y i) ⟨a i ^ 2, sq_nonneg (a i)⟩ μ := by
    intro i _hi
    simpa [Y] using mul_rademacher_hasSubgaussianMGF (ε i) (a i) (hε.1 i)
  simpa [Y, rademacherWeightedSum] using
    (ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun hindep hsub)

/--
The weighted Rademacher sum satisfies the two-sided Hoeffding union bound.

Source: Example 3.1.3, printed p. 114; specification id `example_3_1_3`.
-/
theorem rademacher_weighted_sum_two_sided_union
    (ε : Fin n → Ω → ℝ) (a : Fin n → ℝ)
    (hε : IsRademacherFamily μ ε)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real
        ({ω | t ≤ rademacherWeightedSum ε a ω} ∪
          {ω | rademacherWeightedSum ε a ω ≤ -t}) ≤
      2 * Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2)) := by
  let S := rademacherWeightedSum ε a
  let c : ℝ≥0 := ∑ i, (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)
  have hS : HasSubgaussianMGF S c μ := by
    simpa [S, c] using rademacher_weighted_sum_hasSubgaussianMGF ε a hε
  have hupper : μ.real {ω | t ≤ S ω} ≤ Real.exp (-t ^ 2 / (2 * c)) :=
    hS.measure_ge_le ht
  have hlower : μ.real {ω | S ω ≤ -t} ≤ Real.exp (-t ^ 2 / (2 * c)) := by
    have hneg := hS.neg.measure_ge_le ht
    simpa [S] using hneg
  calc
    μ.real
        ({ω | t ≤ rademacherWeightedSum ε a ω} ∪
          {ω | rademacherWeightedSum ε a ω ≤ -t})
        ≤ μ.real {ω | t ≤ S ω} + μ.real {ω | S ω ≤ -t} := by
          simpa [S] using
            (measureReal_union_le
              (μ := μ) {ω | t ≤ S ω} {ω | S ω ≤ -t})
    _ ≤ Real.exp (-t ^ 2 / (2 * c)) + Real.exp (-t ^ 2 / (2 * c)) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2)) := by
      congr 1
      · ring
      · simp [c]

end RademacherSums

end Chapter03
end InfiniteDimensionalStatistics
