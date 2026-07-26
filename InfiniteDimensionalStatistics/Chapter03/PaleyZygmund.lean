/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.VariationLemmas
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Chapter 3: Paley–Zygmund lower-tail bound

An extended-nonnegative formulation of the Paley–Zygmund argument used in
Proposition 3.2.8.  The theorem avoids division by the second moment: it gives
the equivalent square-root inequality obtained from truncation and Hölder.
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

The moments and probability are `ℝ≥0∞`-valued.  Squaring and dividing by the
finite second moment gives the usual probability lower bound when that moment
is nonzero.
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

end PaleyZygmund

end Chapter03
end InfiniteDimensionalStatistics
