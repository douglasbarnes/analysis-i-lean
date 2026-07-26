/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.RademacherFourthMoment

/-!
# Chapter 3: A lower tail for weighted Rademacher sums

The second- and fourth-moment identities are combined with Paley--Zygmund to
obtain the fixed positive probability used in Proposition 3.2.8.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set Filter

namespace InfiniteDimensionalStatistics
namespace Chapter03

section RademacherLowerBound

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ}

/--
A weighted Rademacher sum exceeds half of its quadratic mean, in squared form,
with probability at least `1/12`.

This is the Paley--Zygmund input used in the lower-bound argument of
Proposition 3.2.8.
-/
theorem one_twelfth_le_measure_rademacherWeightedSum_sq_ge_half
    (ε : Fin n → Ω → ℝ) (a : Fin n → ℝ)
    (hε : IsRademacherFamily μ ε)
    (hvariance : 0 < ∑ i, a i ^ 2) :
    (12 : ℝ≥0∞)⁻¹ ≤
      μ {ω | (∑ i, a i ^ 2) / 2 ≤
        rademacherWeightedSum ε a ω ^ 2} := by
  let S : Ω → ℝ := rademacherWeightedSum ε a
  let V : ℝ := ∑ i, a i ^ 2
  let M4 : ℝ := ∫ ω, S ω ^ 4 ∂μ
  let X : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (S ω ^ 2)
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hVpos : 0 < V := by simpa [V] using hvariance
  have hSmeas : Measurable S := by
    dsimp [S, rademacherWeightedSum]
    fun_prop
  have hSbound : ∀ᵐ ω ∂μ, |S ω| ≤ ∑ i, |a i| := by
    simpa [S, rademacherWeightedSum, finsetRademacherSum] using
      ae_abs_finsetRademacherSum_le
        (a := a) hε.1 (Finset.univ : Finset (Fin n))
  have hCnonneg : 0 ≤ ∑ i, |a i| := by positivity
  have hS2int : Integrable (fun ω => S ω ^ 2) μ :=
    integrable_pow_of_ae_abs_le hSmeas.aemeasurable hCnonneg hSbound 2
  have hS4int : Integrable (fun ω => S ω ^ 4) μ :=
    integrable_pow_of_ae_abs_le hSmeas.aemeasurable hCnonneg hSbound 4
  have hsecondReal : (∫ ω, S ω ^ 2 ∂μ) = V := by
    simpa [S, V] using integral_sq_rademacherWeightedSum ε a hε
  have hfourthUpper : M4 ≤ 3 * V ^ 2 := by
    simpa [S, V, M4] using integral_pow_four_rademacherWeightedSum_le ε a hε
  have hM4nonneg : 0 ≤ M4 := by
    dsimp [M4]
    exact integral_nonneg fun ω => pow_nonneg (S ω) 4
  have hM4pos : 0 < M4 := by
    by_contra h
    have hM4zero : M4 = 0 := le_antisymm (not_lt.mp h) hM4nonneg
    have hzero4 : (fun ω => S ω ^ 4) =ᵐ[μ] 0 := by
      apply (integral_eq_zero_iff_of_nonneg
        (fun ω => pow_nonneg (S ω) 4) hS4int).1
      exact hM4zero
    have hzero2 : (fun ω => S ω ^ 2) =ᵐ[μ] 0 := by
      filter_upwards [hzero4] with ω hω
      have hs : S ω = 0 := by
        simpa only [pow_eq_zero] using hω
      simp [hs]
    have hsecondZero : (∫ ω, S ω ^ 2 ∂μ) = 0 := by
      rw [integral_congr_ae hzero2]
      simp
    linarith [hsecondReal]
  have hXmeas : Measurable X := by
    dsimp [X]
    fun_prop
  have hfirst : (∫⁻ ω, X ω ∂μ) = ENNReal.ofReal V := by
    calc
      (∫⁻ ω, X ω ∂μ) = ENNReal.ofReal (∫ ω, S ω ^ 2 ∂μ) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hS2int
          (ae_of_all μ fun ω => sq_nonneg (S ω))
      _ = ENNReal.ofReal V := by rw [hsecondReal]
  have hpointPow (ω : Ω) :
      X ω ^ (2 : ℝ) = ENNReal.ofReal (S ω ^ 4) := by
    dsimp [X]
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg (S ω)), Real.rpow_two]
    congr 1
    ring
  have hfourth :
      (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ) = ENNReal.ofReal M4 := by
    calc
      (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ)
          = ∫⁻ ω, ENNReal.ofReal (S ω ^ 4) ∂μ := by
              apply lintegral_congr
              exact hpointPow
      _ = ENNReal.ofReal M4 := by
          symm
          exact ofReal_integral_eq_lintegral_ofReal hS4int
            (ae_of_all μ fun ω => pow_nonneg (S ω) 4)
  have hfourth0 : (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ) ≠ 0 := by
    rw [hfourth, ENNReal.ofReal_ne_zero_iff]
    exact hM4pos
  have hfourthTop : (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ) ≠ ∞ := by
    rw [hfourth]
    exact ENNReal.ofReal_ne_top
  have hfirstTop : (∫⁻ ω, X ω ∂μ) ≠ ∞ := by
    rw [hfirst]
    exact ENNReal.ofReal_ne_top
  have hP := paleyZygmund X hXmeas (2 : ℝ≥0∞)⁻¹ (by norm_num)
    hfirstTop hfourth0 hfourthTop
  have hfourthLe :
      (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ) ≤
        3 * (ENNReal.ofReal V) ^ 2 := by
    rw [hfourth]
    calc
      ENNReal.ofReal M4 ≤ ENNReal.ofReal (3 * V ^ 2) :=
        ENNReal.ofReal_le_ofReal hfourthUpper
      _ = 3 * (ENNReal.ofReal V) ^ 2 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hVnonneg]
        norm_num
  have hm0 : ENNReal.ofReal V ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact hVpos
  have hmTop : ENNReal.ofReal V ≠ ∞ := ENNReal.ofReal_ne_top
  have hratio :
      (12 : ℝ≥0∞)⁻¹ ≤
        (((1 - (2 : ℝ≥0∞)⁻¹) * ENNReal.ofReal V) ^ 2 /
          (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ)) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hfourth0) (Or.inl hfourthTop)).2
    calc
      (12 : ℝ≥0∞)⁻¹ * (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ)
          ≤ (12 : ℝ≥0∞)⁻¹ * (3 * (ENNReal.ofReal V) ^ 2) :=
            mul_le_mul_left' hfourthLe _
      _ = ((1 - (2 : ℝ≥0∞)⁻¹) * ENNReal.ofReal V) ^ 2 := by
        field_simp [hm0, hmTop]
        ring
  have hmain := hratio.trans (by simpa [hfirst] using hP)
  have hset :
      {ω | (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal V ≤ X ω} =
        {ω | V / 2 ≤ S ω ^ 2} := by
    ext ω
    dsimp [X]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ)⁻¹),
      ENNReal.ofReal_le_ofReal_iff (sq_nonneg (S ω))]
    norm_num
  rw [hset] at hmain
  simpa [S, V] using hmain

end RademacherLowerBound

end Chapter03
end InfiniteDimensionalStatistics
