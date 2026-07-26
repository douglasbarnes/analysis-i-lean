/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.PseudoMetricLemmas

/-!
# Chapter 3: Elementary canonical U-statistic lemmas

Finite-sum algebra for order-two U-statistics and elementary canonical-kernel
facts that do not depend on the source-sensitive scales in Theorem 3.4.8.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section StatisticAlgebra

variable {S Ω : Type*} [MeasurableSpace S]

/-- The zero kernel gives the zero U-statistic. -/
@[simp] theorem orderTwoUStatistic_zero {n : ℕ}
    (X : Fin n → Ω → S) :
    orderTwoUStatistic X (fun _ _ _ _ => 0) = 0 := by
  funext ω
  simp [orderTwoUStatistic]

/-- Order-two U-statistics are additive in the kernel. -/
theorem orderTwoUStatistic_add {n : ℕ}
    (X : Fin n → Ω → S)
    (h k : Fin n → Fin n → S → S → ℝ) :
    orderTwoUStatistic X (fun i j x y => h i j x y + k i j x y) =
      orderTwoUStatistic X h + orderTwoUStatistic X k := by
  funext ω
  simp [orderTwoUStatistic, Finset.sum_add_distrib]

/-- Order-two U-statistics commute with scalar multiplication of the kernel. -/
theorem orderTwoUStatistic_const_mul {n : ℕ}
    (X : Fin n → Ω → S) (a : ℝ)
    (h : Fin n → Fin n → S → S → ℝ) :
    orderTwoUStatistic X (fun i j x y => a * h i j x y) =
      fun ω => a * orderTwoUStatistic X h ω := by
  funext ω
  simp [orderTwoUStatistic, Finset.mul_sum]

end StatisticAlgebra

section CanonicalKernels

variable {S : Type*} [MeasurableSpace S]

/-- The zero kernel is canonical. -/
@[simp] theorem isCanonicalKernel_zero (P : Measure S) :
    IsCanonicalKernel P (fun _ _ => 0) := by
  constructor <;> intro x <;> simp [IsCanonicalInFirstCoordinate,
    IsCanonicalInSecondCoordinate]

/-- For a symmetric kernel, first-coordinate degeneracy implies second-coordinate degeneracy. -/
theorem IsCanonicalInFirstCoordinate.second_of_symmetric
    (P : Measure S) {h : S → S → ℝ}
    (hfirst : IsCanonicalInFirstCoordinate P h)
    (hsymm : ∀ x y, h x y = h y x) :
    IsCanonicalInSecondCoordinate P h := by
  intro x
  calc
    (∫ y, h x y ∂P) = ∫ y, h y x ∂P := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact hsymm x y
    _ = 0 := hfirst x

/-- A symmetric kernel canonical in its first coordinate is canonical. -/
theorem IsCanonicalKernel.of_first_of_symmetric
    (P : Measure S) {h : S → S → ℝ}
    (hfirst : IsCanonicalInFirstCoordinate P h)
    (hsymm : ∀ x y, h x y = h y x) :
    IsCanonicalKernel P h :=
  ⟨hfirst, hfirst.second_of_symmetric P hsymm⟩

/-- Uniform kernel-scale bounds are monotone in the scale. -/
theorem HasUniformKernelScale.mono {n : ℕ}
    {h : Fin n → Fin n → S → S → ℝ} {A A' : ℝ≥0}
    (hA : HasUniformKernelScale h A) (hAA' : A ≤ A') :
    HasUniformKernelScale h A' := by
  intro i j x y hij
  exact (hA i j x y hij).trans (by exact_mod_cast hAA')

/-- The zero kernel has uniform scale zero. -/
@[simp] theorem hasUniformKernelScale_zero {n : ℕ} :
    HasUniformKernelScale
      (fun (_i _j : Fin n) (_x _y : S) => 0) 0 := by
  intro i j x y hij
  simp

end CanonicalKernels

end Chapter03
end InfiniteDimensionalStatistics
