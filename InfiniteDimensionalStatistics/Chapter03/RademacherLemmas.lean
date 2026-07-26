/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.EntropyMethodLemmas

/-!
# Chapter 3: Elementary Rademacher lemmas

Closure of the Rademacher law under negation, its almost-sure unit magnitude
and square, and deterministic algebra for weighted Rademacher sums.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section SingleRademacher

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {ε : Ω → ℝ}

/-- The negative of a Rademacher variable is Rademacher. -/
theorem IsRademacher.neg (hε : IsRademacher P ε) :
    IsRademacher P (fun ω => -ε ω) := by
  refine ⟨hε.1.neg, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hε.2.1] with ω hω
    rcases hω with hneg | hpos
    · exact Or.inr (by simp [hneg])
    · exact Or.inl (by simp [hpos])
  · simpa only [neg_eq_iff_eq_neg, neg_one] using hε.2.2.2.1
  · simpa only [neg_eq_neg_iff] using hε.2.2.1
  · rw [integral_neg, hε.2.2.2.2, neg_zero]

/-- A Rademacher variable has absolute value one almost surely. -/
theorem IsRademacher.ae_abs_eq_one (hε : IsRademacher P ε) :
    ∀ᵐ ω ∂P, |ε ω| = 1 := by
  filter_upwards [hε.2.1] with ω hω
  rcases hω with hneg | hpos <;> simp [hneg, hpos]

/-- A Rademacher variable has square one almost surely. -/
theorem IsRademacher.ae_sq_eq_one (hε : IsRademacher P ε) :
    ∀ᵐ ω ∂P, ε ω ^ 2 = 1 := by
  filter_upwards [hε.2.1] with ω hω
  rcases hω with hneg | hpos <;> simp [hneg, hpos]

/-- A Rademacher variable is almost surely nonzero. -/
theorem IsRademacher.ae_ne_zero (hε : IsRademacher P ε) :
    ∀ᵐ ω ∂P, ε ω ≠ 0 := by
  filter_upwards [hε.2.1] with ω hω
  rcases hω with hneg | hpos <;> simp [hneg, hpos]

end SingleRademacher

section Families

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {n : ℕ}

/-- Every coordinate in a Rademacher family has square one almost surely. -/
theorem IsRademacherFamily.ae_forall_sq_eq_one
    {ε : Fin n → Ω → ℝ} (hε : IsRademacherFamily P ε) :
    ∀ᵐ ω ∂P, ∀ i, ε i ω ^ 2 = 1 := by
  rw [ae_all_iff]
  intro i
  exact (hε.1 i).ae_sq_eq_one

/-- Zero deterministic weights give the zero weighted sum. -/
@[simp] theorem rademacherWeightedSum_zero
    (ε : Fin n → Ω → ℝ) :
    rademacherWeightedSum ε (fun _ => 0) = 0 := by
  funext ω
  simp [rademacherWeightedSum]

/-- Weighted Rademacher sums are additive in their deterministic coefficients. -/
theorem rademacherWeightedSum_add
    (ε : Fin n → Ω → ℝ) (a b : Fin n → ℝ) :
    rademacherWeightedSum ε (fun i => a i + b i) =
      rademacherWeightedSum ε a + rademacherWeightedSum ε b := by
  funext ω
  simp [rademacherWeightedSum, add_mul, Finset.sum_add_distrib]

/-- Common scalar factors pull out of a weighted Rademacher sum. -/
theorem rademacherWeightedSum_const_mul
    (ε : Fin n → Ω → ℝ) (c : ℝ) (a : Fin n → ℝ) :
    rademacherWeightedSum ε (fun i => c * a i) =
      fun ω => c * rademacherWeightedSum ε a ω := by
  funext ω
  simp [rademacherWeightedSum, ← mul_assoc, Finset.mul_sum]

end Families

end Chapter03
end InfiniteDimensionalStatistics
