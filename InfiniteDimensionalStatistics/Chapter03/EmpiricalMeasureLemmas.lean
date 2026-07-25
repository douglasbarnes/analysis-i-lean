/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.OuterMeasureLemmas
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Chapter 3: Empirical-measure calculus

Evaluation and integration identities for equation (3.1).  The positive sample
size hypothesis is explicit whenever the normalisation is simplified to one.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section EmpiricalMeasure

variable {S : Type*} [MeasurableSpace S]

/-- Evaluation of the empirical measure on a measurable set. -/
theorem empiricalMeasure_apply {n : ℕ} (X : Fin n → S)
    (A : Set S) (hA : MeasurableSet A) :
    empiricalMeasure X A =
      (n : ℝ≥0∞)⁻¹ * ∑ i, if X i ∈ A then 1 else 0 := by
  simp [empiricalMeasure, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_apply]

/-- The empirical measure has total mass one for a nonempty sample. -/
theorem empiricalMeasure_univ {n : ℕ} (X : Fin n → S) (hn : 0 < n) :
    empiricalMeasure X Set.univ = 1 := by
  rw [empiricalMeasure_apply X Set.univ MeasurableSet.univ]
  simp [hn.ne']

/--
Bochner integration against the empirical measure equals the displayed finite
average.
-/
theorem integral_empiricalMeasure {n : ℕ} (X : Fin n → S)
    (f : S → ℝ) (hf : StronglyMeasurable f) :
    (∫ x, f x ∂empiricalMeasure X) = empiricalMean X f := by
  rw [empiricalMeasure, integral_smul_measure]
  rw [integral_finsetSum_measure]
  · simp [empiricalMean, integral_dirac' f _ hf]
  · intro i _hi
    exact integrable_dirac' hf (by simp)

/-- The notation `Qf` applied to the empirical measure is the empirical mean. -/
theorem measureIntegral_empiricalMeasure {n : ℕ} (X : Fin n → S)
    (f : S → ℝ) (hf : StronglyMeasurable f) :
    measureIntegral (empiricalMeasure X) f = empiricalMean X f := by
  exact integral_empiricalMeasure X f hf

/-- The centred process is the normalised finite sum of centred evaluations. -/
theorem centredEmpiricalProcess_eq_sum {n : ℕ}
    (P : Measure S) (X : Fin n → S) (𝓕 : Set (S → ℝ))
    (f : 𝓕) :
    centredEmpiricalProcess P X 𝓕 f =
      (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i, (f.1 (X i) - measureIntegral P f.1) := by
  by_cases hn : n = 0
  · subst hn
    simp [centredEmpiricalProcess, empiricalMean]
  · rw [centredEmpiricalProcess, empiricalMean]
    have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by
      positivity
    field_simp
    ring

end EmpiricalMeasure

end Chapter03
end InfiniteDimensionalStatistics
