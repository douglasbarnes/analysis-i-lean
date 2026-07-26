/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.ProductGeometryLemmas

/-!
# Chapter 3: Entropy-growth lemmas

Elementary positivity and monotonicity results for the regular, uniform,
polynomial and lower entropy-growth predicates from Section 3.5.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section RegularMajorants

/-- The regular entropy primitive is nonnegative. -/
theorem RegularEntropyMajorant.primitive_nonneg
    (h : RegularEntropyMajorant) (δ : ℝ) :
    0 ≤ h.primitive δ := by
  unfold RegularEntropyMajorant.primitive
  apply integral_nonneg
  intro t
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) δ
  · simp [Set.indicator_of_mem ht, Real.sqrt_nonneg]
  · simp [Set.indicator_of_notMem ht]

/-- The regular entropy primitive vanishes at radius zero. -/
@[simp] theorem RegularEntropyMajorant.primitive_zero
    (h : RegularEntropyMajorant) :
    h.primitive 0 = 0 := by
  simp [RegularEntropyMajorant.primitive]

end RegularMajorants

section UniformMajorants

variable {S : Type*} [MeasurableSpace S]
variable {𝓕 : Set (S → ℝ)} {F : S → ℝ}

/-- A larger entropy majorant preserves a uniform entropy bound. -/
theorem HasUniformEntropyMajorant.mono_H
    {H H' : ℝ → ℝ}
    (h : HasUniformEntropyMajorant 𝓕 F H)
    (hHH' : ∀ x, H x ≤ H' x) :
    HasUniformEntropyMajorant 𝓕 F H' := by
  intro Q hQ ε hε
  exact (h Q hQ ε hε).trans <|
    Nat.floor_mono (Real.exp_le_exp.mpr (hHH' (1 / ε)))

/-- Increasing the polynomial entropy constant preserves the entropy bound. -/
theorem HasPolynomialUniformEntropy.mono_A
    {A A' v : ℝ}
    (h : HasPolynomialUniformEntropy 𝓕 F A v)
    (hA : 0 ≤ A) (hAA' : A ≤ A') (hv : 0 ≤ v) :
    HasPolynomialUniformEntropy 𝓕 F A' v := by
  intro Q hQ ε hε hε1
  apply (h Q hQ ε hε hε1).trans
  apply Nat.floor_mono
  apply Real.rpow_le_rpow
  · exact div_nonneg hA hε.le
  · exact div_le_div_of_nonneg_right hAA' hε.le
  · exact hv

end UniformMajorants

section Fullness

variable {S : Type*} [MeasurableSpace S]
variable {𝓕 : Set (S → ℝ)} {P : Measure S}
variable {H : ℝ → ℝ} {F : S → ℝ}

/-- Weakening the positive lower-growth constant preserves fullness. -/
theorem IsFullForEntropy.mono_constant
    {c c' εmin εmax : ℝ}
    (hfull : IsFullForEntropy 𝓕 P H F c εmin εmax)
    (hc' : 0 < c') (hcc' : c' ≤ c)
    (hH : ∀ x, 0 ≤ H x) :
    IsFullForEntropy 𝓕 P H F c' εmin εmax := by
  refine ⟨hc', hfull.2.1, hfull.2.2.1, ?_⟩
  intro ε hmin hmax
  exact (Real.exp_le_exp.mpr <|
    mul_le_mul_of_nonneg_right hcc'
      (hH (measureL2Seminorm P F / ε))).trans
    (hfull.2.2.2 ε hmin hmax)

/-- Replacing the lower-growth function by a smaller nonnegative function preserves fullness. -/
theorem IsFullForEntropy.mono_function
    {H' : ℝ → ℝ} {c εmin εmax : ℝ}
    (hfull : IsFullForEntropy 𝓕 P H F c εmin εmax)
    (hc : 0 ≤ c) (hH'H : ∀ x, H' x ≤ H x) :
    IsFullForEntropy 𝓕 P H' F c εmin εmax := by
  refine ⟨hfull.1, hfull.2.1, hfull.2.2.1, ?_⟩
  intro ε hmin hmax
  exact (Real.exp_le_exp.mpr <|
    mul_le_mul_of_nonneg_left
      (hH'H (measureL2Seminorm P F / ε)) hc).trans
    (hfull.2.2.2 ε hmin hmax)

end Fullness

end Chapter03
end InfiniteDimensionalStatistics
