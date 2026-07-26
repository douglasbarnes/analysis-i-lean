/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.UniformityLemmas

/-!
# Chapter 3: Product-geometry order lemmas

Order-theoretic properties of weighted distance, Talagrand's convex distance,
disagreement sets and Euclidean distance from zero.  These are independent of
the convex-distance concentration theorem.
-/

noncomputable section

open Set
open scoped BigOperators ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section WeightedDistance

variable {S : Type*} {n : ℕ}

/-- Weighted distance to a set is nonnegative. -/
theorem weightedDistanceToSet_nonneg
    (α : Fin n → ℝ) (x : Fin n → S) (A : Set (Fin n → S)) :
    0 ≤ weightedDistanceToSet α x A :=
  bot_le

/-- Enlarging the target set can only decrease weighted distance. -/
theorem weightedDistanceToSet_antitone
    (α : Fin n → ℝ) (x : Fin n → S)
    {A B : Set (Fin n → S)} (hAB : A ⊆ B) :
    weightedDistanceToSet α x B ≤ weightedDistanceToSet α x A := by
  unfold weightedDistanceToSet
  refine le_iInf fun y => ?_
  exact iInf_le_of_le (⟨y.1, hAB y.2⟩ : B) le_rfl

/-- The weighted distance from a member of a set to that set is zero. -/
@[simp] theorem weightedDistanceToSet_eq_zero_of_mem
    (α : Fin n → ℝ) {x : Fin n → S} {A : Set (Fin n → S)}
    (hx : x ∈ A) :
    weightedDistanceToSet α x A = 0 := by
  apply le_antisymm
  · unfold weightedDistanceToSet
    exact (iInf_le_of_le (⟨x, hx⟩ : A) <| by
      simp [weightedHammingDistance])
  · exact bot_le

end WeightedDistance

section ConvexDistance

variable {S : Type*} {n : ℕ}

/-- Talagrand's convex distance is nonnegative. -/
theorem convexDistance_nonneg (x : Fin n → S) (A : Set (Fin n → S)) :
    0 ≤ convexDistance x A :=
  bot_le

/-- Enlarging the target set can only decrease convex distance. -/
theorem convexDistance_antitone
    (x : Fin n → S) {A B : Set (Fin n → S)} (hAB : A ⊆ B) :
    convexDistance x B ≤ convexDistance x A := by
  unfold convexDistance
  refine iSup_le fun α => ?_
  exact (weightedDistanceToSet_antitone α.1 x hAB).trans
    (le_iSup (fun β : euclideanUnitSphere (n := n) =>
      weightedDistanceToSet β.1 x A) α)

/-- Convex distance vanishes at every point of the target set. -/
@[simp] theorem convexDistance_eq_zero_of_mem
    {x : Fin n → S} {A : Set (Fin n → S)} (hx : x ∈ A) :
    convexDistance x A = 0 := by
  apply le_antisymm
  · unfold convexDistance
    refine iSup_le fun α => ?_
    exact (weightedDistanceToSet_eq_zero_of_mem α.1 hx).le
  · exact bot_le

/-- Disagreement sets are monotone in the underlying product set. -/
theorem disagreementSet_mono
    (x : Fin n → S) {A B : Set (Fin n → S)} (hAB : A ⊆ B) :
    disagreementSet x A ⊆ disagreementSet x B := by
  rintro u ⟨y, hy, rfl⟩
  exact ⟨y, hAB hy, rfl⟩

/-- The zero disagreement vector occurs when the base point belongs to the set. -/
theorem zero_mem_disagreementSet
    {x : Fin n → S} {A : Set (Fin n → S)} (hx : x ∈ A) :
    (0 : Fin n → ℝ) ∈ disagreementSet x A := by
  refine ⟨x, hx, ?_⟩
  funext i
  simp [disagreementVector]

end ConvexDistance

section EuclideanDistance

variable {n : ℕ}

/-- The finite Euclidean norm is nonnegative. -/
theorem euclideanNorm_nonneg (u : Fin n → ℝ) :
    0 ≤ euclideanNorm u :=
  Real.sqrt_nonneg _

/-- The Euclidean norm of the zero vector is zero. -/
@[simp] theorem euclideanNorm_zero :
    euclideanNorm (0 : Fin n → ℝ) = 0 := by
  simp [euclideanNorm]

/-- Enlarging a vector set can only decrease its distance from zero. -/
theorem euclideanDistanceFromZero_antitone
    {A B : Set (Fin n → ℝ)} (hAB : A ⊆ B) :
    euclideanDistanceFromZero B ≤ euclideanDistanceFromZero A := by
  unfold euclideanDistanceFromZero
  refine le_iInf fun u => ?_
  exact iInf_le_of_le (⟨u.1, hAB u.2⟩ : B) le_rfl

/-- A set containing zero has zero Euclidean distance from zero. -/
@[simp] theorem euclideanDistanceFromZero_eq_zero_of_zero_mem
    {A : Set (Fin n → ℝ)} (h0 : (0 : Fin n → ℝ) ∈ A) :
    euclideanDistanceFromZero A = 0 := by
  apply le_antisymm
  · unfold euclideanDistanceFromZero
    exact iInf_le_of_le (⟨0, h0⟩ : A) (by simp)
  · exact bot_le

end EuclideanDistance

end Chapter03
end InfiniteDimensionalStatistics
