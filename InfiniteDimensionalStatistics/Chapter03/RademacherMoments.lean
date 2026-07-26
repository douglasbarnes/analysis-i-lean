/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.PaleyZygmund
import Mathlib.Probability.Moments.Variance

/-!
# Chapter 3: Moments of weighted Rademacher sums

Exact first and second moments of finite weighted Rademacher sums.  Together
with `paleyZygmund_holder`, these supply the principal moment input to
Proposition 3.2.8.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section WeightedSums

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : ℕ}

/-- A deterministic multiple of a Rademacher variable has variance `a²`. -/
theorem variance_mul_rademacher
    (ε : Ω → ℝ) (a : ℝ) (hε : IsRademacher μ ε) :
    Var[fun ω => a * ε ω; μ] = a ^ 2 := by
  have hmem : MemLp (fun ω => a * ε ω) 2 μ :=
    memLp_of_bounded (mul_rademacher_mem_Icc ε a hε)
      hε.1.aestronglyMeasurable.const_mul 2
  rw [variance_of_integral_eq_zero hmem.aemeasurable
    (integral_mul_rademacher_eq_zero ε a hε)]
  calc
    (∫ ω, (a * ε ω) ^ 2 ∂μ) = ∫ _ω, a ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hε.ae_sq_eq_one] with ω hω
      rw [mul_pow, hω, mul_one]
    _ = a ^ 2 := by simp

/-- A weighted Rademacher sum is centred. -/
theorem integral_rademacherWeightedSum_eq_zero
    (ε : Fin n → Ω → ℝ) (a : Fin n → ℝ)
    (hε : IsRademacherFamily μ ε) :
    (∫ ω, rademacherWeightedSum ε a ω ∂μ) = 0 := by
  unfold rademacherWeightedSum
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero fun i _hi =>
      integral_mul_rademacher_eq_zero (ε i) (a i) (hε.1 i)
  · intro i _hi
    exact (memLp_of_bounded
      (mul_rademacher_mem_Icc (ε i) (a i) (hε.1 i))
      (hε.1 i).1.aestronglyMeasurable.const_mul 2).integrable (by simp)

/-- A weighted Rademacher sum belongs to `L²`. -/
theorem memLp_two_rademacherWeightedSum
    (ε : Fin n → Ω → ℝ) (a : Fin n → ℝ)
    (hε : IsRademacherFamily μ ε) :
    MemLp (rademacherWeightedSum ε a) 2 μ := by
  unfold rademacherWeightedSum
  apply memLp_finsetSum'
  intro i _hi
  exact memLp_of_bounded
    (mul_rademacher_mem_Icc (ε i) (a i) (hε.1 i))
    (hε.1 i).1.aestronglyMeasurable.const_mul 2

/-- The variance of a weighted independent Rademacher sum is `∑ᵢ aᵢ²`. -/
theorem variance_rademacherWeightedSum
    (ε : Fin n → Ω → ℝ) (a : Fin n → ℝ)
    (hε : IsRademacherFamily μ ε) :
    Var[rademacherWeightedSum ε a; μ] = ∑ i, a i ^ 2 := by
  let Y : Fin n → Ω → ℝ := fun i ω => a i * ε i ω
  have hY : ∀ i ∈ (Finset.univ : Finset (Fin n)), MemLp (Y i) 2 μ := by
    intro i _hi
    exact memLp_of_bounded
      (mul_rademacher_mem_Icc (ε i) (a i) (hε.1 i))
      (hε.1 i).1.aestronglyMeasurable.const_mul 2
  have hindep : Set.Pairwise (↑(Finset.univ : Finset (Fin n)))
      (fun i j => Y i ⟂ᵢ[μ] Y j) := by
    intro i hi j hj hij
    exact (hε.2.indepFun hij).comp (by fun_prop) (by fun_prop)
  simpa [Y, rademacherWeightedSum, variance_mul_rademacher] using
    (ProbabilityTheory.IndepFun.variance_sum hY hindep)

/-- Exact second moment of a weighted independent Rademacher sum. -/
theorem integral_sq_rademacherWeightedSum
    (ε : Fin n → Ω → ℝ) (a : Fin n → ℝ)
    (hε : IsRademacherFamily μ ε) :
    (∫ ω, (rademacherWeightedSum ε a ω) ^ 2 ∂μ) =
      ∑ i, a i ^ 2 := by
  have hmem := memLp_two_rademacherWeightedSum ε a hε
  rw [← variance_of_integral_eq_zero hmem.aemeasurable
    (integral_rademacherWeightedSum_eq_zero ε a hε)]
  exact variance_rademacherWeightedSum ε a hε

end WeightedSums

end Chapter03
end InfiniteDimensionalStatistics
