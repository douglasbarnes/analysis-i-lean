/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.VCStructuralLemmas

/-!
# Chapter 3: Elementary bounded-variation lemmas

Algebraic invariance of partition variation and `p`-variation under output
translation and negation, together with elementary membership facts for the
translate and affine transform classes.
-/

noncomputable section

open Set
open scoped BigOperators ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section VariationAlgebra

/-- Adding a constant to the values of a function does not change partition variation. -/
theorem partitionVariationPower_add_const
    (f : ℝ → ℝ) (c p : ℝ) (π : IncreasingPartition) :
    partitionVariationPower (fun x => f x + c) p π =
      partitionVariationPower f p π := by
  unfold partitionVariationPower
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  ring

/-- Negating a function does not change partition variation. -/
theorem partitionVariationPower_neg
    (f : ℝ → ℝ) (p : ℝ) (π : IncreasingPartition) :
    partitionVariationPower (fun x => -f x) p π =
      partitionVariationPower f p π := by
  unfold partitionVariationPower
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  rw [show -f (π.point i.succ) - -f (π.point i.castSucc) =
      -(f (π.point i.succ) - f (π.point i.castSucc)) by ring,
    abs_neg]

/-- Adding a constant does not change `p`-variation. -/
theorem pVariation_add_const (f : ℝ → ℝ) (c p : ℝ) :
    pVariation (fun x => f x + c) p = pVariation f p := by
  unfold pVariation
  simp_rw [partitionVariationPower_add_const]

/-- Negating a function does not change `p`-variation. -/
theorem pVariation_neg (f : ℝ → ℝ) (p : ℝ) :
    pVariation (fun x => -f x) p = pVariation f p := by
  unfold pVariation
  simp_rw [partitionVariationPower_neg]

/-- Bounded `p`-variation is invariant under adding an output constant. -/
theorem hasBoundedPVariation_add_const_iff
    (f : ℝ → ℝ) (c p : ℝ) :
    HasBoundedPVariation (fun x => f x + c) p ↔
      HasBoundedPVariation f p := by
  simp [HasBoundedPVariation, pVariation_add_const]

/-- Bounded `p`-variation is invariant under negation. -/
theorem hasBoundedPVariation_neg_iff
    (f : ℝ → ℝ) (p : ℝ) :
    HasBoundedPVariation (fun x => -f x) p ↔
      HasBoundedPVariation f p := by
  simp [HasBoundedPVariation, pVariation_neg]

end VariationAlgebra

section TransformClasses

/-- A function belongs to its own translate class. -/
theorem mem_translateClass_self (f : ℝ → ℝ) :
    f ∈ translateClass f := by
  refine ⟨0, ?_⟩
  funext x
  simp [translateFunction]

/-- The translate class is contained in the affine transform class. -/
theorem translateClass_subset_affineTransformClass (f : ℝ → ℝ) :
    translateClass f ⊆ affineTransformClass f := by
  rintro g ⟨a, rfl⟩
  refine ⟨1, 1, a, ?_⟩
  funext x
  simp [translateFunction, affineTransformFunction]

/-- A function belongs to its own affine transform class. -/
theorem mem_affineTransformClass_self (f : ℝ → ℝ) :
    f ∈ affineTransformClass f :=
  translateClass_subset_affineTransformClass f (mem_translateClass_self f)

/-- Every affine transform of the zero function is zero. -/
@[simp] theorem affineTransformClass_zero :
    affineTransformClass (fun _ => 0) = {(fun _ => 0)} := by
  ext g
  constructor
  · rintro ⟨a, s, t, rfl⟩
    simp [affineTransformFunction]
  · intro hg
    have : g = fun _ => 0 := by simpa using hg
    subst g
    exact ⟨0, 0, 0, by simp [affineTransformFunction]⟩

end TransformClasses

end Chapter03
end InfiniteDimensionalStatistics
