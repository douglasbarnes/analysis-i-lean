/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.UStatisticLemmas

/-!
# Chapter 3: Elementary entropy-method lemmas

Algebraic closure properties of coordinate-insensitive statistics,
self-bounding statistics and bounded-difference bounds.  These facts are
independent of the tensorisation and concentration theorems.
-/

noncomputable section

open Set
open scoped BigOperators ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section CoordinateInsensitivity

variable {S : Type*} {n : ℕ}

/-- Constant statistics ignore every coordinate. -/
theorem ignoresCoordinate_const (c : ℝ) (k : Fin n) :
    IgnoresCoordinate (fun _ : Fin n → S => c) k := by
  intro x y hxy
  rfl

/-- Sums of coordinate-insensitive statistics remain coordinate-insensitive. -/
theorem IgnoresCoordinate.add
    {Z W : (Fin n → S) → ℝ} {k : Fin n}
    (hZ : IgnoresCoordinate Z k) (hW : IgnoresCoordinate W k) :
    IgnoresCoordinate (fun x => Z x + W x) k := by
  intro x y hxy
  rw [hZ x y hxy, hW x y hxy]

/-- Scalar multiples preserve coordinate insensitivity. -/
theorem IgnoresCoordinate.const_mul
    {Z : (Fin n → S) → ℝ} {k : Fin n}
    (hZ : IgnoresCoordinate Z k) (a : ℝ) :
    IgnoresCoordinate (fun x => a * Z x) k := by
  intro x y hxy
  rw [hZ x y hxy]

/-- Coordinate oscillation is always nonnegative. -/
theorem coordinateOscillation_nonneg
    (Z : (Fin n → S) → ℝ) (k : Fin n) (x : Fin n → S) :
    0 ≤ coordinateOscillation Z k x :=
  bot_le

/-- The zero statistic has zero coordinate oscillation. -/
@[simp] theorem coordinateOscillation_zero
    (k : Fin n) (x : Fin n → S) :
    coordinateOscillation (fun _ : Fin n → S => 0) k x = 0 := by
  simp [coordinateOscillation]

end CoordinateInsensitivity

section BoundedDifferences

variable {S : Type*} {n : ℕ}

/-- Bounded-difference bounds are monotone in their coordinate constants. -/
theorem HasBoundedDifferences.mono
    {Z : (Fin n → S) → ℝ} {c d : Fin n → ℝ}
    (hZ : HasBoundedDifferences Z c) (hcd : ∀ k, c k ≤ d k) :
    HasBoundedDifferences Z d := by
  constructor
  · intro k
    exact (hZ.1 k).trans (hcd k)
  · intro k x y hxy
    exact (hZ.2 k x y hxy).trans (hcd k)

/-- Constant statistics have zero bounded differences. -/
@[simp] theorem hasBoundedDifferences_const (a : ℝ) :
    HasBoundedDifferences (fun _ : Fin n → S => a) (fun _ => 0) := by
  constructor
  · intro k
    exact le_rfl
  · intro k x y hxy
    simp

/-- Sums of bounded-difference statistics have the summed coordinate bounds. -/
theorem HasBoundedDifferences.add
    {Z W : (Fin n → S) → ℝ} {c d : Fin n → ℝ}
    (hZ : HasBoundedDifferences Z c)
    (hW : HasBoundedDifferences W d) :
    HasBoundedDifferences (fun x => Z x + W x) (fun k => c k + d k) := by
  constructor
  · intro k
    exact add_nonneg (hZ.1 k) (hW.1 k)
  · intro k x y hxy
    calc
      |(Z x + W x) - (Z y + W y)| =
          |(Z x - Z y) + (W x - W y)| := by ring_nf
      _ ≤ |Z x - Z y| + |W x - W y| := abs_add _ _
      _ ≤ c k + d k := add_le_add (hZ.2 k x y hxy) (hW.2 k x y hxy)

/-- Scalar multiplication scales bounded-difference constants by `|a|`. -/
theorem HasBoundedDifferences.const_mul
    {Z : (Fin n → S) → ℝ} {c : Fin n → ℝ}
    (hZ : HasBoundedDifferences Z c) (a : ℝ) :
    HasBoundedDifferences (fun x => a * Z x) (fun k => |a| * c k) := by
  constructor
  · intro k
    exact mul_nonneg (abs_nonneg a) (hZ.1 k)
  · intro k x y hxy
    calc
      |a * Z x - a * Z y| = |a| * |Z x - Z y| := by
        rw [← mul_sub, abs_mul]
      _ ≤ |a| * c k := mul_le_mul_of_nonneg_left (hZ.2 k x y hxy) (abs_nonneg a)

/-- The bounded-differences variance proxy is nonnegative. -/
theorem boundedDifferencesVarianceProxy_nonneg (c : Fin n → ℝ) :
    0 ≤ boundedDifferencesVarianceProxy c := by
  unfold boundedDifferencesVarianceProxy
  exact Finset.sum_nonneg fun k _ => sq_nonneg (c k)

/-- The zero coordinate bound has zero variance proxy. -/
@[simp] theorem boundedDifferencesVarianceProxy_zero :
    boundedDifferencesVarianceProxy (fun _ : Fin n => 0) = 0 := by
  simp [boundedDifferencesVarianceProxy]

end BoundedDifferences

section SelfBounding

variable {S : Type*} {n : ℕ}

/-- The zero statistic with zero deletion statistics is self-bounding. -/
@[simp] theorem isSelfBounding_zero :
    IsSelfBounding
      (fun _ : Fin n → S => 0)
      (fun _ _ => 0) := by
  simp [IsSelfBounding, IgnoresCoordinate, coordinateDecrement]

end SelfBounding

end Chapter03
end InfiniteDimensionalStatistics
