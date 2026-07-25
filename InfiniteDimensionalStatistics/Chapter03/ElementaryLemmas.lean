/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.WeakConvergence

/-!
# Chapter 3: Elementary proved lemmas

Facts following directly from the Chapter 3 definitions.  These are genuine
proofs; no axiom, placeholder, or hidden proof is introduced.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Empirical

variable {S : Type*} [MeasurableSpace S]

/-- The empirical mean of the empty sample is zero. -/
theorem empiricalMean_empty (X : Fin 0 → S) (f : S → ℝ) :
    empiricalMean X f = 0 := by
  simp [empiricalMean]

/-- The kernel estimator is definitionally the displayed finite sum from (3.4). -/
theorem kernelDensityEstimator_eq_sum {n : ℕ} (X : Fin n → ℝ)
    (K : ℝ → ℝ) (h x : ℝ) :
    kernelDensityEstimator X K h x =
      (n : ℝ)⁻¹ * ∑ i, h⁻¹ * K ((x - X i) / h) := by
  rfl

end Empirical

section ConcentrationDefinitions

/-- Hamming distance vanishes on the diagonal. -/
theorem hammingDistance_self {n : ℕ} (x : Fin n → Bool) :
    hammingDistance x x = 0 := by
  simp [hammingDistance]

/-- Hamming distance is symmetric. -/
theorem hammingDistance_comm {n : ℕ} (x y : Fin n → Bool) :
    hammingDistance x y = hammingDistance y x := by
  simp [hammingDistance, ne_comm]

/-- Bennett's function vanishes at zero. -/
theorem bennettFunction_zero : bennettFunction 0 = 0 := by
  simp [bennettFunction]

/-- Outer probability of the empty event is zero. -/
theorem outerProbability_empty {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) : outerProbability P ∅ = 0 := by
  simp [outerProbability]

end ConcentrationDefinitions

section SymmetricAndStarHulls

variable {S : Type*}

/-- Every class is contained in its symmetric hull. -/
theorem subset_symmetricHull (𝓕 : Set (S → ℝ)) :
    𝓕 ⊆ symmetricHull 𝓕 := by
  intro f hf
  exact Set.mem_union_left _ hf

/-- The negative of every member lies in the symmetric hull. -/
theorem neg_mem_symmetricHull {𝓕 : Set (S → ℝ)} {f : S → ℝ}
    (hf : f ∈ 𝓕) : (fun x ↦ -f x) ∈ symmetricHull 𝓕 := by
  right
  exact ⟨f, hf, rfl⟩

/-- Every class is contained in its star hull. -/
theorem subset_starHull (𝓕 : Set (S → ℝ)) :
    𝓕 ⊆ starHull 𝓕 := by
  intro f hf
  refine ⟨1, by norm_num, f, hf, ?_⟩
  funext x
  simp

end SymmetricAndStarHulls

section VC

variable {α : Type*}

/-- Every trace is a subset of the finite set on which it is taken. -/
theorem setClassTrace_subset_powerset (𝓒 : Set (Set α)) (A : Finset α) :
    setClassTrace 𝓒 A ⊆ Set.powerset (A : Set α) := by
  intro B hB
  rcases hB with ⟨C, _hC, rfl⟩
  exact Set.inter_subset_right

/-- Indicator classes have the constant-one envelope. -/
theorem indicatorClass_hasEnvelope (𝓒 : Set (Set α)) :
    IsEnvelope (indicatorClass 𝓒) (fun _ ↦ 1) := by
  intro f hf x
  rcases hf with ⟨C, _hC, rfl⟩
  by_cases hx : x ∈ C <;> simp [hx]

end VC

section WeakConvergenceDefinitions

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

/-- Bounded-Lipschitz distance from a measure to itself is zero. -/
theorem boundedLipschitzDistance_self (P : Measure E) :
    boundedLipschitzDistance P P = 0 := by
  simp [boundedLipschitzDistance]

end WeakConvergenceDefinitions

end Chapter03
end InfiniteDimensionalStatistics
