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

/-- Bennett's function is strictly positive away from zero on `[0,∞)`. -/
theorem bennettFunction_pos {u : ℝ} (hu : 0 < u) :
    0 < bennettFunction u := by
  have hpos : 0 < 1 + u := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have hleft : (1 + u) * (1 - (1 + u)⁻¹) = u := by
    field_simp
    ring
  rw [hleft] at hmul
  have hstrict := Real.log_lt_sub_one_of_pos hpos (by linarith)
  unfold bennettFunction
  have : u < (1 + u) * Real.log (1 + u) := by
    by_contra h
    have hle : (1 + u) * Real.log (1 + u) ≤ u := le_of_not_gt h
    exact (not_lt_of_ge hle) (lt_of_le_of_ne hmul (by
      intro heq
      have : Real.log (1 + u) = u / (1 + u) := by
        apply (mul_left_cancel₀ hpos.ne')
        field_simp at heq ⊢
        linarith
      have hcontra : Real.log (1 + u) < u := by simpa using hstrict
      linarith))
  linarith

end BennettFunction

section EntropyPhi

/-- The entropy-method function `φ(x)=e^{-x}-1+x` is nonnegative. -/
theorem entropyPhi_nonneg (x : ℝ) : 0 ≤ entropyPhi x := by
  have h := Real.add_one_le_exp (-x)
  unfold entropyPhi
  linarith

/-- The entropy-method function is bounded above by `x² e^{|x|}/2`. -/
theorem entropyPhi_le_exp_abs_mul_sq (x : ℝ) :
    entropyPhi x ≤ Real.exp |x| * x ^ 2 := by
  have hexp : Real.exp (-x) ≤ Real.exp |x| := by
    exact Real.exp_le_exp.mpr (neg_le_abs x)
  have hlin : -1 + x ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1 / 2)]
  unfold entropyPhi
  calc
    Real.exp (-x) - 1 + x ≤ Real.exp |x| - 1 + x := by linarith
    _ ≤ Real.exp |x| + x ^ 2 := by linarith
    _ ≤ Real.exp |x| * x ^ 2 := by
      by_cases hx : |x| ≤ 1
      · have hexp_one : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
        nlinarith [sq_nonneg x]
      · have hx1 : 1 < |x| := lt_of_not_ge hx
        have hx2 : 1 < x ^ 2 := by nlinarith [sq_abs x]
        have hexp_one : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
        nlinarith

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
