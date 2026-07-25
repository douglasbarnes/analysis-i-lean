/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.AnalyticLemmas

/-!
# Chapter 3: Finite sub-Gaussian maxima

The common-proxy specialization of Theorem 3.1.10.  The result retains the
positive Chernoff parameter explicitly; optimizing that scalar expression is a
separate elementary calculation.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section FiniteSubgaussianMaximum

variable {Ω ι : Type*} [MeasurableSpace Ω]
  [Fintype ι] [Nonempty ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Z : ι → Ω → ℝ} {M : Ω → ℝ}

/--
Common sub-Gaussian proxy bound for a finite maximum:
`E M ≤ λ⁻¹ (log |ι| + σ² λ²/2)`.

Source: Theorem 3.1.10, printed p. 121; specification id `theorem_3_1_10`.
-/
theorem integral_max_le_subgaussian_parameter
    (σ2 : ℝ≥0) {λ : ℝ} (hλ : 0 < λ)
    (hmax : IsPointwiseFiniteMaximum Z M)
    (hM : Integrable M μ)
    (hExpM : Integrable (fun ω ↦ Real.exp (λ * M ω)) μ)
    (hZ : ∀ i, HasSubgaussianMGF (Z i) σ2 μ) :
    (∫ ω, M ω ∂μ) ≤
      λ⁻¹ *
        (Real.log (Fintype.card ι : ℝ) + (σ2 : ℝ) * λ ^ 2 / 2) := by
  have hraw := integral_max_le_log_sum_mgf
    hλ hmax hM hExpM (fun i ↦ (hZ i).integrable_exp_mul λ)
  have hsum :
      ∑ i, mgf (Z i) μ λ ≤
        (Fintype.card ι : ℝ) * Real.exp ((σ2 : ℝ) * λ ^ 2 / 2) := by
    calc
      ∑ i, mgf (Z i) μ λ
          ≤ ∑ i, Real.exp ((σ2 : ℝ) * λ ^ 2 / 2) := by
            exact Finset.sum_le_sum fun i _hi ↦ (hZ i).mgf_le λ
      _ = (Fintype.card ι : ℝ) *
          Real.exp ((σ2 : ℝ) * λ ^ 2 / 2) := by
            simp [mul_comm]
  have hsum_pos : 0 < ∑ i, mgf (Z i) μ λ := by
    obtain ⟨j⟩ := ‹Nonempty ι›
    have hj : 0 < mgf (Z j) μ λ := mgf_pos ((hZ j).integrable_exp_mul λ)
    exact lt_of_lt_of_le hj
      (Finset.single_le_sum (fun i _hi ↦ mgf_nonneg) (Finset.mem_univ j))
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hrhs_pos :
      0 < (Fintype.card ι : ℝ) *
        Real.exp ((σ2 : ℝ) * λ ^ 2 / 2) :=
    mul_pos hcard_pos (Real.exp_pos _)
  have hlog :
      Real.log (∑ i, mgf (Z i) μ λ) ≤
        Real.log ((Fintype.card ι : ℝ) *
          Real.exp ((σ2 : ℝ) * λ ^ 2 / 2)) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hsum_pos) (Set.mem_Ioi.mpr hrhs_pos) hsum
  calc
    (∫ ω, M ω ∂μ)
        ≤ λ⁻¹ * Real.log (∑ i, mgf (Z i) μ λ) := hraw
    _ ≤ λ⁻¹ *
        Real.log ((Fintype.card ι : ℝ) *
          Real.exp ((σ2 : ℝ) * λ ^ 2 / 2)) := by
      gcongr
      exact inv_nonneg.mpr hλ.le
    _ = λ⁻¹ *
        (Real.log (Fintype.card ι : ℝ) + (σ2 : ℝ) * λ ^ 2 / 2) := by
      rw [Real.log_mul (ne_of_gt hcard_pos) (Real.exp_ne_zero _), Real.log_exp]

end FiniteSubgaussianMaximum

end Chapter03
end InfiniteDimensionalStatistics
