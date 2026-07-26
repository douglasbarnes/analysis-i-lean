/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.Bennett
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Chapter 3: Bennett's bounded-variable mgf estimate

This file proves Theorem 3.1.5.  The proof follows the book's moment-series
argument: expand the mgf, remove the centred linear term, bound every higher
moment by `c^(k-2) E X²`, and resum the exponential remainder.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section BoundedMoments

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} {c λ v : ℝ}

/-- Every power of an almost surely bounded measurable real random variable is integrable. -/
theorem integrable_pow_of_ae_abs_le
    (hX : AEMeasurable X μ) (hc : 0 ≤ c)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ c) (k : ℕ) :
    Integrable (fun ω => X ω ^ k) μ := by
  refine (integrable_const (c ^ k)).mono' ?_ ?_
  · exact (AEMeasurable.pow_const hX k).aestronglyMeasurable
  · filter_upwards [hbound] with ω hω
    simp only [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg (X ω)) hω k

/-- Exponential remainder as the tail of its power series. -/
theorem exp_sub_one_sub_eq_tsum (z : ℝ) :
    Real.exp z - 1 - z = ∑' n : ℕ, z ^ (n + 2) / (n + 2)! := by
  have hs : Summable (fun n : ℕ => z ^ n / n !) := Real.summable_pow_div_factorial z
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hexp : (∑' n : ℕ, z ^ n / n !) = Real.exp z := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    simp [smul_eq_mul, div_eq_mul_inv]
  rw [hexp] at hsplit
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
    Nat.factorial_one] at hsplit
  linarith

/--
Moment expansion of the mgf of an almost surely bounded random variable.
-/
theorem mgf_eq_tsum_moments_of_ae_abs_le
    (hX : AEMeasurable X μ) (hc : 0 ≤ c)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ c) (λ : ℝ) :
    mgf X μ λ =
      ∑' k : ℕ, (λ ^ k / k !) * (∫ ω, X ω ^ k ∂μ) := by
  let F : ℕ → Ω → ℝ := fun k ω => (λ * X ω) ^ k / k !
  let A : ℝ := |λ| * c
  have hF_int : ∀ k, Integrable (F k) μ := by
    intro k
    refine (integrable_const (A ^ k / k !)).mono' ?_ ?_
    · exact ((AEMeasurable.const_mul hX λ).pow_const k).aestronglyMeasurable.div_const _
    · filter_upwards [hbound] with ω hω
      simp only [F, A, Real.norm_eq_abs, abs_div, abs_pow, abs_mul,
        abs_natCast, abs_of_nonneg hc]
      gcongr
  have hF_sum : Summable (fun k => ∫ ω, ‖F k ω‖ ∂μ) := by
    refine Summable.of_nonneg_of_le
      (fun k => integral_nonneg fun _ => norm_nonneg _) ?_
      (Real.summable_pow_div_factorial A)
    intro k
    calc
      (∫ ω, ‖F k ω‖ ∂μ) ≤ ∫ _ω, A ^ k / k ! ∂μ := by
        apply integral_mono_ae (hF_int k).norm (integrable_const _)
        filter_upwards [hbound] with ω hω
        simp only [F, A, Real.norm_eq_abs, abs_div, abs_pow, abs_mul,
          abs_natCast, abs_of_nonneg hc]
        gcongr
      _ = A ^ k / k ! := by simp
  have hpoint : ∀ ω, Real.exp (λ * X ω) = ∑' k, F k ω := by
    intro ω
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    simp [F, smul_eq_mul, div_eq_mul_inv]
  calc
    mgf X μ λ = ∫ ω, Real.exp (λ * X ω) ∂μ := rfl
    _ = ∫ ω, ∑' k, F k ω ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ hpoint
    _ = ∑' k, ∫ ω, F k ω ∂μ :=
      (integral_tsum_of_summable_integral_norm hF_int hF_sum).symm
    _ = ∑' k : ℕ, (λ ^ k / k !) * (∫ ω, X ω ^ k ∂μ) := by
      apply tsum_congr
      intro k
      have hfun : F k = fun ω => (λ ^ k / k !) * X ω ^ k := by
        funext ω
        simp only [F, mul_pow]
        ring
      rw [hfun, integral_const_mul]

/-- Higher moments are controlled by the second moment and the uniform bound. -/
theorem abs_integral_pow_le_bound_mul_second
    (hX : AEMeasurable X μ) (hc : 0 ≤ c)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ c)
    {k : ℕ} (hk : 2 ≤ k) :
    |∫ ω, X ω ^ k ∂μ| ≤
      c ^ (k - 2) * ∫ ω, X ω ^ 2 ∂μ := by
  have hkint := integrable_pow_of_ae_abs_le hX hc hbound k
  have h2int := integrable_pow_of_ae_abs_le hX hc hbound 2
  calc
    |∫ ω, X ω ^ k ∂μ| ≤ ∫ ω, |X ω ^ k| ∂μ :=
      abs_integral_le_integral_abs _
    _ ≤ ∫ ω, c ^ (k - 2) * X ω ^ 2 ∂μ := by
      apply integral_mono_ae hkint.abs (h2int.const_mul _)
      filter_upwards [hbound] with ω hω
      calc
        |X ω ^ k| = |X ω| ^ k := abs_pow _ _
        _ = |X ω| ^ (k - 2) * |X ω| ^ 2 := by
          rw [← pow_add, Nat.sub_add_cancel hk]
        _ ≤ c ^ (k - 2) * |X ω| ^ 2 := by
          gcongr
        _ = c ^ (k - 2) * X ω ^ 2 := by
          rw [sq_abs]
    _ = c ^ (k - 2) * ∫ ω, X ω ^ 2 ∂μ := by
      rw [integral_const_mul]

end BoundedMoments

section BennettTheorem

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} {c v : ℝ}

/--
**Bennett's mgf inequality (Theorem 3.1.5).**

If `X` is centred, `|X| ≤ c` almost surely and `E X² = v`, then its
one-sided mgf satisfies Bennett's exact exponential bound.
-/
theorem hasBennettMGF_of_ae_abs_le
    (hX : AEMeasurable X μ)
    (hc : 0 < c)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ c)
    (hmean : (∫ ω, X ω ∂μ) = 0)
    (hsecond : (∫ ω, X ω ^ 2 ∂μ) = v) :
    HasBennettMGF μ X v c := by
  have hv : 0 ≤ v := by
    rw [← hsecond]
    exact integral_nonneg fun ω => sq_nonneg (X ω)
  constructor
  · intro λ _hλ
    have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-c) c := by
      filter_upwards [hbound] with ω hω
      simpa [abs_le] using hω
    exact integrable_exp_mul_of_mem_Icc hX hIcc
  · intro λ hλ
    let a : ℕ → ℝ := fun k =>
      (λ ^ k / k !) * (∫ ω, X ω ^ k ∂μ)
    have ha_sum : Summable a := by
      have hdom : Summable (fun k => (|λ| * c) ^ k / k !) :=
        Real.summable_pow_div_factorial (|λ| * c)
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg (a k)) ?_ hdom
      intro k
      have hkint := integrable_pow_of_ae_abs_le hX hc.le hbound k
      calc
        ‖a k‖ ≤ (|λ| ^ k / k !) * |∫ ω, X ω ^ k ∂μ| := by
          simp [a, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_natCast]
        _ ≤ (|λ| ^ k / k !) * c ^ k := by
          gcongr
          calc
            |∫ ω, X ω ^ k ∂μ| ≤ ∫ ω, |X ω ^ k| ∂μ :=
              abs_integral_le_integral_abs _
            _ ≤ ∫ _ω, c ^ k ∂μ := by
              apply integral_mono_ae hkint.abs (integrable_const _)
              filter_upwards [hbound] with ω hω
              simp only [abs_pow]
              exact pow_le_pow_left₀ (abs_nonneg (X ω)) hω k
            _ = c ^ k := by simp
        _ = (|λ| * c) ^ k / k ! := by ring
    have hmgf := mgf_eq_tsum_moments_of_ae_abs_le hX hc.le hbound λ
    rw [hmgf, ← ha_sum.sum_add_tsum_nat_add 2]
    have htail_le :
        (∑' n : ℕ, a (n + 2)) ≤
          (v / c ^ 2) * (Real.exp (λ * c) - 1 - λ * c) := by
      let b : ℕ → ℝ := fun n =>
        (v / c ^ 2) * ((λ * c) ^ (n + 2) / (n + 2)!)
      have hb_sum : Summable b := by
        have hbase : Summable (fun n : ℕ =>
            (λ * c) ^ (n + 2) / (n + 2)!) := by
          exact (Real.summable_pow_div_factorial (λ * c)).comp_injective
            (fun _ _ h => Nat.add_right_cancel h)
        exact hbase.mul_left (v / c ^ 2)
      calc
        (∑' n : ℕ, a (n + 2)) ≤ ∑' n : ℕ, b n := by
          apply tsum_le_tsum
          · intro n
            have hmoment := abs_integral_pow_le_bound_mul_second
              hX hc.le hbound (k := n + 2) (by omega)
            have hmoment' :
                (∫ ω, X ω ^ (n + 2) ∂μ) ≤ c ^ n * v := by
              calc
                (∫ ω, X ω ^ (n + 2) ∂μ)
                    ≤ |∫ ω, X ω ^ (n + 2) ∂μ| := le_abs_self _
                _ ≤ c ^ ((n + 2) - 2) * ∫ ω, X ω ^ 2 ∂μ := hmoment
                _ = c ^ n * v := by simp [hsecond]
            have hcoef : 0 ≤ λ ^ (n + 2) / (n + 2)! := by positivity
            calc
              a (n + 2) ≤ (λ ^ (n + 2) / (n + 2)!) * (c ^ n * v) := by
                exact mul_le_mul_of_nonneg_left hmoment' hcoef
              _ = b n := by
                dsimp [b]
                field_simp [hc.ne']
                ring
          · exact ha_sum.comp_injective (fun _ _ h => Nat.add_right_cancel h)
          · exact hb_sum
        _ = (v / c ^ 2) * (Real.exp (λ * c) - 1 - λ * c) := by
          rw [← tsum_mul_left]
          congr 1
          exact exp_sub_one_sub_eq_tsum (λ * c)
    have hhead : (∑ k ∈ Finset.range 2, a k) = 1 := by
      simp [a, hmean]
    rw [hhead]
    calc
      1 + ∑' n : ℕ, a (n + 2)
          ≤ 1 + (v / c ^ 2) * (Real.exp (λ * c) - 1 - λ * c) :=
        add_le_add_left htail_le 1
      _ ≤ Real.exp ((v / c ^ 2) * (Real.exp (λ * c) - λ * c - 1)) := by
        simpa [sub_sub, add_comm, add_left_comm, add_assoc] using
          Real.add_one_le_exp ((v / c ^ 2) * (Real.exp (λ * c) - λ * c - 1))

end BennettTheorem

end Chapter03
end InfiniteDimensionalStatistics
