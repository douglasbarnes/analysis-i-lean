/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.VCBooleanTrace

/-!
# Chapter 3: Empirical-measure algebra

Linearity and probability-mass facts for the empirical measure and empirical
mean from equation (3.1).
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section EmpiricalMean

variable {S : Type*}

/-- Empirical means preserve addition. -/
theorem empiricalMean_add {n : ℕ} (X : Fin n → S)
    (f g : S → ℝ) :
    empiricalMean X (fun x ↦ f x + g x) =
      empiricalMean X f + empiricalMean X g := by
  simp [empiricalMean, Finset.sum_add_distrib]
  ring

/-- Empirical means preserve scalar multiplication. -/
theorem empiricalMean_const_mul {n : ℕ} (X : Fin n → S)
    (a : ℝ) (f : S → ℝ) :
    empiricalMean X (fun x ↦ a * f x) = a * empiricalMean X f := by
  simp [empiricalMean, ← Finset.mul_sum]
  ring

/-- Empirical means preserve negation. -/
theorem empiricalMean_neg {n : ℕ} (X : Fin n → S)
    (f : S → ℝ) :
    empiricalMean X (fun x ↦ -f x) = -empiricalMean X f := by
  simpa using empiricalMean_const_mul X (-1) f

/-- Empirical means preserve subtraction. -/
theorem empiricalMean_sub {n : ℕ} (X : Fin n → S)
    (f g : S → ℝ) :
    empiricalMean X (fun x ↦ f x - g x) =
      empiricalMean X f - empiricalMean X g := by
  simpa [sub_eq_add_neg] using
    empiricalMean_add X f (fun x ↦ -g x)

/-- The empirical mean of a constant is that constant for a nonempty sample. -/
theorem empiricalMean_const {n : ℕ} (X : Fin n → S)
    (hn : 0 < n) (c : ℝ) :
    empiricalMean X (fun _ ↦ c) = c := by
  simp [empiricalMean, hn.ne']

end EmpiricalMean

section EmpiricalMeasure

variable {S : Type*} [MeasurableSpace S]

/-- A nonempty empirical measure is a probability measure. -/
theorem empiricalMeasure_isProbabilityMeasure {n : ℕ}
    (X : Fin n → S) (hn : 0 < n) :
    IsProbabilityMeasure (empiricalMeasure X) :=
  ⟨empiricalMeasure_univ X hn⟩

/-- The empirical measure of the empty sample is the zero measure. -/
theorem empiricalMeasure_empty (X : Fin 0 → S) :
    empiricalMeasure X = 0 := by
  simp [empiricalMeasure]

end EmpiricalMeasure

section CentredFunctional

variable {S : Type*} [MeasurableSpace S]

/-- Source-level centred empirical functional, independent of an index class. -/
def centredEmpiricalFunctional {n : ℕ}
    (P : Measure S) (X : Fin n → S) (f : S → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * (empiricalMean X f - measureIntegral P f)

/-- The centred empirical functional is additive. -/
theorem centredEmpiricalFunctional_add {n : ℕ}
    (P : Measure S) (X : Fin n → S) (f g : S → ℝ)
    (hf : Integrable f P) (hg : Integrable g P) :
    centredEmpiricalFunctional P X (fun x ↦ f x + g x) =
      centredEmpiricalFunctional P X f +
        centredEmpiricalFunctional P X g := by
  rw [centredEmpiricalFunctional, centredEmpiricalFunctional,
    centredEmpiricalFunctional, empiricalMean_add,
    integral_add hf hg]
  ring

/-- The centred empirical functional is homogeneous. -/
theorem centredEmpiricalFunctional_const_mul {n : ℕ}
    (P : Measure S) (X : Fin n → S) (a : ℝ) (f : S → ℝ) :
    centredEmpiricalFunctional P X (fun x ↦ a * f x) =
      a * centredEmpiricalFunctional P X f := by
  rw [centredEmpiricalFunctional, centredEmpiricalFunctional,
    empiricalMean_const_mul, integral_const_mul]
  ring

end CentredFunctional

end Chapter03
end InfiniteDimensionalStatistics
