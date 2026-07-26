/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.VariationLemmas
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Chapter 3: Paley–Zygmund lower-tail bound

Extended-nonnegative formulations of the Paley–Zygmund argument used in
Proposition 3.2.8.  The square-root theorem is the direct truncation/Hölder
estimate; the divided theorem derives the standard probability lower bound
under explicit nonzero finite second-moment hypotheses.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section PaleyZygmund

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/--
Paley–Zygmund in square-root form.  For a measurable nonnegative random
variable `X`, a threshold factor `θ ≤ 1`, and finite first moment,

`(1-θ) E X ≤ (E X²)^(1/2) P{θ E X ≤ X}^(1/2)`.
-/
theorem paleyZygmund_holder
    (X : Ω → ℝ≥0∞) (hX : Measurable X)
    (θ : ℝ≥0∞) (hθ : θ ≤ 1)
    (hm : (∫⁻ ω, X ω ∂μ) ≠ ∞) :
    (1 - θ) * (∫⁻ ω, X ω ∂μ) ≤
      (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (μ {ω | θ * (∫⁻ z, X z ∂μ) ≤ X ω}) ^ (1 / (2 : ℝ)) := by
  let m : ℝ≥0∞ := ∫⁻ ω, X ω ∂μ
  let A : Set Ω := {ω | θ * m ≤ X ω}
  have hA : MeasurableSet A := by
    exact measurableSet_le measurable_const hX
  have hθfin : θ ≠ ∞ := ne_top_of_le_ne_top (by simp) hθ
  have hθmfin : θ * m ≠ ∞ := ENNReal.mul_ne_top hθfin hm
  have hcomp : ∫⁻ ω in Aᶜ, X ω ∂μ ≤ θ * m := by
    calc
      ∫⁻ ω in Aᶜ, X ω ∂μ ≤ ∫⁻ _ω in Aᶜ, θ * m ∂μ := by
        apply setLIntegral_mono' hA.compl
        intro ω hω
        have hn : ¬ θ * m ≤ X ω := by simpa [A] using hω
        exact le_of_lt (lt_of_not_ge hn)
      _ = θ * m * μ Aᶜ := by simp
      _ ≤ θ * m * 1 := by
        apply mul_le_mul_left'
        calc
          μ Aᶜ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      _ = θ * m := by simp
  have hθmle : θ * m ≤ m := by
    calc
      θ * m ≤ 1 * m := mul_le_mul_right' hθ m
      _ = m := one_mul m
  have hlower : (1 - θ) * m ≤ ∫⁻ ω in A, X ω ∂μ := by
    rw [tsub_mul, one_mul]
    apply (tsub_le_iff_right hθmle).2
    calc
      m = (∫⁻ ω in A, X ω ∂μ) + ∫⁻ ω in Aᶜ, X ω ∂μ :=
        (lintegral_add_compl X hA).symm
      _ ≤ (∫⁻ ω in A, X ω ∂μ) + θ * m :=
        add_le_add_left hcomp _
  let g : Ω → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hg : Measurable g := (measurable_indicator_const_iff (1 : ℝ≥0∞)).2 hA
  have hprod :
      (∫⁻ ω, X ω * g ω ∂μ) = ∫⁻ ω in A, X ω ∂μ := by
    rw [← lintegral_indicator hA]
    apply lintegral_congr
    intro ω
    by_cases hω : ω ∈ A <;> simp [g, hω]
  have hgpow :
      (∫⁻ ω, g ω ^ (2 : ℝ) ∂μ) = μ A := by
    calc
      (∫⁻ ω, g ω ^ (2 : ℝ) ∂μ) = ∫⁻ ω, g ω ∂μ := by
        apply lintegral_congr
        intro ω
        by_cases hω : ω ∈ A <;> simp [g, hω]
      _ = μ A := by
        simp [g, lintegral_indicator_one hA]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    Real.HolderConjugate.two_two hX.aemeasurable hg.aemeasurable
  rw [hprod, hgpow] at hholder
  change (1 - θ) * m ≤ _
  exact hlower.trans hholder

/--
Standard divided Paley–Zygmund bound.  When the second moment is nonzero and
finite,

`((1-θ) E X)² / E(X²) ≤ P{θ E X ≤ X}`.
-/
theorem paleyZygmund
    (X : Ω → ℝ≥0∞) (hX : Measurable X)
    (θ : ℝ≥0∞) (hθ : θ ≤ 1)
    (hm : (∫⁻ ω, X ω ∂μ) ≠ ∞)
    (hsq0 : (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ) ≠ 0)
    (hsqtop : (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ) ≠ ∞) :
    ((1 - θ) * (∫⁻ ω, X ω ∂μ)) ^ 2 /
        (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ) ≤
      μ {ω | θ * (∫⁻ z, X z ∂μ) ≤ X ω} := by
  let m : ℝ≥0∞ := ∫⁻ ω, X ω ∂μ
  let s2 : ℝ≥0∞ := ∫⁻ ω, X ω ^ (2 : ℝ) ∂μ
  let p : ℝ≥0∞ := μ {ω | θ * m ≤ X ω}
  have hroot :
      (1 - θ) * m ≤ s2 ^ (1 / (2 : ℝ)) * p ^ (1 / (2 : ℝ)) := by
    simpa [m, s2, p] using paleyZygmund_holder X hX θ hθ hm
  have half_square (x : ℝ≥0∞) :
      x ^ (1 / (2 : ℝ)) * x ^ (1 / (2 : ℝ)) = x := by
    rw [← ENNReal.rpow_add_of_nonneg (1 / (2 : ℝ)) (1 / (2 : ℝ))
      (by positivity) (by positivity)]
    norm_num
  have hsquare : ((1 - θ) * m) ^ 2 ≤ s2 * p := by
    rw [pow_two]
    calc
      (1 - θ) * m * ((1 - θ) * m) ≤
          (s2 ^ (1 / (2 : ℝ)) * p ^ (1 / (2 : ℝ))) *
            (s2 ^ (1 / (2 : ℝ)) * p ^ (1 / (2 : ℝ))) :=
        mul_le_mul hroot hroot bot_le bot_le
      _ =
          (s2 ^ (1 / (2 : ℝ)) * s2 ^ (1 / (2 : ℝ))) *
            (p ^ (1 / (2 : ℝ)) * p ^ (1 / (2 : ℝ))) := by
        ac_rfl
      _ = s2 * p := by rw [half_square, half_square]
  change ((1 - θ) * m) ^ 2 / s2 ≤ p
  apply (ENNReal.div_le_iff_le_mul (Or.inl hsq0) (Or.inl hsqtop)).2
  simpa [mul_comm] using hsquare

end PaleyZygmund

end Chapter03
end InfiniteDimensionalStatistics
