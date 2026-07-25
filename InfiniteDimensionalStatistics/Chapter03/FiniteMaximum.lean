/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.Bennett
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Chapter 3: Finite maxima from mgf bounds

The log-sum-exp argument underlying Theorem 3.1.10.  The maximum is supplied by
an explicit pointwise attainment predicate, so the result is independent of a
particular finite-maximum implementation.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

/-- `M` is the pointwise maximum of the finite family `Z`. -/
def IsPointwiseFiniteMaximum {Ω ι : Type*} [Fintype ι]
    (Z : ι → Ω → ℝ) (M : Ω → ℝ) : Prop :=
  ∀ ω, (∀ i, Z i ω ≤ M ω) ∧ ∃ i, M ω = Z i ω

section MaximalMGF

variable {Ω ι : Type*} [MeasurableSpace Ω]
  [Fintype ι] [Nonempty ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Z : ι → Ω → ℝ} {M : Ω → ℝ} {λ : ℝ}

/--
Exponential form of the finite maximal inequality:
`exp(λ E M) ≤ ∑ᵢ E exp(λ Zᵢ)`.
-/
theorem exp_mul_integral_max_le_sum_mgf
    (hλ : 0 ≤ λ)
    (hmax : IsPointwiseFiniteMaximum Z M)
    (hM : Integrable M μ)
    (hExpM : Integrable (fun ω ↦ Real.exp (λ * M ω)) μ)
    (hExpZ : ∀ i, Integrable (fun ω ↦ Real.exp (λ * Z i ω)) μ) :
    Real.exp (λ * ∫ ω, M ω ∂μ) ≤
      ∑ i, mgf (Z i) μ λ := by
  have hJensen :
      Real.exp (∫ ω, λ * M ω ∂μ) ≤
        ∫ ω, Real.exp (λ * M ω) ∂μ := by
    have hlin : Integrable (fun ω ↦ λ * M ω) μ := hM.const_mul λ
    have hexp : Integrable (Real.exp ∘ fun ω ↦ λ * M ω) μ := by
      simpa [Function.comp_def] using hExpM
    simpa using
      (convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
        (ae_of_all μ fun _ ↦ Set.mem_univ _) hlin hexp)
  have hpointwise : ∀ ω,
      Real.exp (λ * M ω) ≤ ∑ i, Real.exp (λ * Z i ω) := by
    intro ω
    rcases (hmax ω).2 with ⟨j, hj⟩
    rw [hj]
    exact Finset.single_le_sum (fun i _hi ↦ Real.exp_nonneg (λ * Z i ω))
      (Finset.mem_univ j)
  have hsumInt : Integrable (fun ω ↦ ∑ i, Real.exp (λ * Z i ω)) μ :=
    integrable_finset_sum _ fun i _hi ↦ hExpZ i
  calc
    Real.exp (λ * ∫ ω, M ω ∂μ)
        = Real.exp (∫ ω, λ * M ω ∂μ) := by
          rw [integral_const_mul]
    _ ≤ ∫ ω, Real.exp (λ * M ω) ∂μ := hJensen
    _ ≤ ∫ ω, ∑ i, Real.exp (λ * Z i ω) ∂μ :=
      integral_mono hExpM hsumInt hpointwise
    _ = ∑ i, mgf (Z i) μ λ := by
      rw [integral_finset_sum]
      rfl

/--
The logarithmic maximal inequality of Theorem 3.1.10.

Source: Theorem 3.1.10, printed p. 121; specification id `theorem_3_1_10`.
-/
theorem integral_max_le_log_sum_mgf
    (hλ : 0 < λ)
    (hmax : IsPointwiseFiniteMaximum Z M)
    (hM : Integrable M μ)
    (hExpM : Integrable (fun ω ↦ Real.exp (λ * M ω)) μ)
    (hExpZ : ∀ i, Integrable (fun ω ↦ Real.exp (λ * Z i ω)) μ) :
    (∫ ω, M ω ∂μ) ≤
      λ⁻¹ * Real.log (∑ i, mgf (Z i) μ λ) := by
  have hExp := exp_mul_integral_max_le_sum_mgf hλ.le hmax hM hExpM hExpZ
  have hsum_pos : 0 < ∑ i, mgf (Z i) μ λ := by
    obtain ⟨j⟩ := ‹Nonempty ι›
    have hj : 0 < mgf (Z j) μ λ := mgf_pos (hExpZ j)
    exact lt_of_lt_of_le hj (Finset.single_le_sum (fun i _hi ↦ mgf_nonneg) (Finset.mem_univ j))
  have hlog : λ * (∫ ω, M ω ∂μ) ≤
      Real.log (∑ i, mgf (Z i) μ λ) := by
    rw [← Real.exp_le_exp, Real.exp_log hsum_pos]
    exact hExp
  calc
    (∫ ω, M ω ∂μ) = λ⁻¹ * (λ * ∫ ω, M ω ∂μ) := by field_simp
    _ ≤ λ⁻¹ * Real.log (∑ i, mgf (Z i) μ λ) := by
      gcongr
      exact inv_nonneg.mpr hλ.le

end MaximalMGF

end Chapter03
end InfiniteDimensionalStatistics
