/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.ConvergenceInDistribution

/-!
# Chapter 3: Elementary analytic inequalities

Basic inequalities for Bennett's function, the entropy-method function
`φ(x)=e^{-x}-1+x`, product distances, and variation.  These are genuine
analytic or algebraic proofs and do not assert any unproved concentration
principle.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section BennettFunction

/-- Bennett's function is nonnegative on the nonnegative half-line. -/
theorem bennettFunction_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ bennettFunction u := by
  have hpos : 0 < 1 + u := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have hleft : (1 + u) * (1 - (1 + u)⁻¹) = u := by
    field_simp
    ring
  rw [hleft] at hmul
  unfold bennettFunction
  linarith

/-- A simple quadratic upper bound for Bennett's function. -/
theorem bennettFunction_le_sq {u : ℝ} (hu : 0 ≤ u) :
    bennettFunction u ≤ u ^ 2 := by
  have hpos : 0 < 1 + u := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  unfold bennettFunction
  nlinarith

end BennettFunction

section EntropyPhi

/-- The entropy-method function `φ(x)=e^{-x}-1+x` is nonnegative. -/
theorem entropyPhi_nonneg (x : ℝ) : 0 ≤ entropyPhi x := by
  have h := Real.add_one_le_exp (-x)
  unfold entropyPhi
  linarith

end EntropyPhi

section ProductGeometry

variable {S : Type*} {n : ℕ}

@[simp] theorem weightedHammingDistance_self
    (α : Fin n → ℝ) (x : Fin n → S) :
    weightedHammingDistance α x x = 0 := by
  simp [weightedHammingDistance]

/-- Weighted Hamming distance is symmetric. -/
theorem weightedHammingDistance_comm
    (α : Fin n → ℝ) (x y : Fin n → S) :
    weightedHammingDistance α x y = weightedHammingDistance α y x := by
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases h : x i = y i
  · simp [h]
  · simp [h, Ne.symm h]

@[simp] theorem disagreementVector_self (x : Fin n → S) :
    disagreementVector x x = 0 := by
  funext i
  simp [disagreementVector]

end ProductGeometry

section Variation

/-- Constant functions have zero partition variation. -/
@[simp] theorem partitionVariationPower_const
    (c p : ℝ) (π : IncreasingPartition) :
    partitionVariationPower (fun _ ↦ c) p π = 0 := by
  simp [partitionVariationPower]

/-- Constant functions have zero `p`-variation. -/
@[simp] theorem pVariation_const (c p : ℝ) :
    pVariation (fun _ ↦ c) p = 0 := by
  simp [pVariation]

end Variation

end Chapter03
end InfiniteDimensionalStatistics
