/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.Tightness

/-!
# Chapter 3: Exact VC permanence facts

Complementation preserves traces, shattering, and VC dimension exactly.  This
is one source-exact component of Proposition 3.6.7.  The source-blocked
quantitative bounds for finite unions and intersections are not guessed here.
-/

noncomputable section

open scoped BigOperators
open Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

variable {α : Type*}

/-- Set class obtained by complementing every member. -/
def complementClass (𝓒 : Set (Set α)) : Set (Set α) :=
  (fun C : Set α ↦ Cᶜ) '' 𝓒

/-- Complement relative to the finite sample `A`. -/
def relativeComplement (A : Finset α) (B : Set α) : Set α :=
  (A : Set α) \ B

/-- A relative complement is contained in the finite ambient set. -/
theorem relativeComplement_subset (A : Finset α) (B : Set α) :
    relativeComplement A B ⊆ (A : Set α) :=
  diff_subset

/-- Complementing a class preserves shattering of a fixed finite set. -/
theorem shatters_complementClass_iff
    (𝓒 : Set (Set α)) (A : Finset α) :
    Shatters (complementClass 𝓒) A ↔ Shatters 𝓒 A := by
  constructor
  · intro hcomp
    unfold Shatters at hcomp ⊢
    ext B
    constructor
    · exact setClassTrace_subset_powerset 𝓒 A
    · intro hBA
      have hrel : relativeComplement A B ⊆ (A : Set α) :=
        relativeComplement_subset A B
      have hrelTrace : relativeComplement A B ∈
          setClassTrace (complementClass 𝓒) A := by
        rw [hcomp]
        exact hrel
      rcases hrelTrace with ⟨C, ⟨D, hD, rfl⟩, hC⟩
      refine ⟨D, hD, ?_⟩
      ext x
      constructor
      · rintro ⟨hxD, hxA⟩
        by_contra hxB
        have hxRel : x ∈ relativeComplement A B := ⟨hxA, hxB⟩
        have hxComp : x ∈ Dᶜ ∩ (A : Set α) := by
          rw [hC]
          exact hxRel
        exact hxComp.1 hxD
      · intro hxB
        have hxA : x ∈ (A : Set α) := hBA hxB
        refine ⟨?_, hxA⟩
        by_contra hxD
        have hxComp : x ∈ Dᶜ ∩ (A : Set α) := ⟨hxD, hxA⟩
        have hxRel : x ∈ relativeComplement A B := by
          rw [← hC]
          exact hxComp
        exact hxRel.2 hxB
  · intro h
    unfold Shatters at h ⊢
    ext B
    constructor
    · exact setClassTrace_subset_powerset (complementClass 𝓒) A
    · intro hBA
      have hrel : relativeComplement A B ⊆ (A : Set α) :=
        relativeComplement_subset A B
      have hrelTrace : relativeComplement A B ∈ setClassTrace 𝓒 A := by
        rw [h]
        exact hrel
      rcases hrelTrace with ⟨D, hD, hDrel⟩
      refine ⟨Dᶜ, ⟨D, hD, rfl⟩, ?_⟩
      ext x
      constructor
      · rintro ⟨hxDc, hxA⟩
        by_contra hxB
        have hxRel : x ∈ relativeComplement A B := ⟨hxA, hxB⟩
        have hxD : x ∈ D ∩ (A : Set α) := by
          rw [hDrel]
          exact hxRel
        exact hxDc hxD.1
      · intro hxB
        have hxA : x ∈ (A : Set α) := hBA hxB
        refine ⟨?_, hxA⟩
        intro hxD
        have hxDinter : x ∈ D ∩ (A : Set α) := ⟨hxD, hxA⟩
        have hxRel : x ∈ relativeComplement A B := by
          rw [← hDrel]
          exact hxDinter
        exact hxRel.2 hxB

/-- Complementation preserves VC dimension exactly. -/
theorem vcDimension_complementClass (𝓒 : Set (Set α)) :
    vcDimension (complementClass 𝓒) = vcDimension 𝓒 := by
  unfold vcDimension
  congr 1
  ext k
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, (shatters_complementClass_iff 𝓒 A).mp hA, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, (shatters_complementClass_iff 𝓒 A).mpr hA, rfl⟩

/-- Finite VC dimension is preserved by complementation. -/
theorem isVCClass_complement_iff (𝓒 : Set (Set α)) :
    IsVCClass (complementClass 𝓒) ↔ IsVCClass 𝓒 := by
  simp [IsVCClass, vcDimension_complementClass]

end Chapter03
end InfiniteDimensionalStatistics
