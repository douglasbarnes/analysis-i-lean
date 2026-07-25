/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.SubgaussianMaximum
import Mathlib.Data.Finset.NAry

/-!
# Chapter 3: Boolean trace bounds

Exact finite-trace cardinal estimates for pairwise intersections and unions of
set classes.  They form the combinatorial core of the corresponding clauses of
Proposition 3.6.7.  The source-blocked quantitative VC-index constants are not
asserted here.
-/

noncomputable section

open Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

variable {α : Type*}

/-- Pairwise intersection class. -/
def intersectionClass (𝓒 𝓓 : Set (Set α)) : Set (Set α) :=
  {E | ∃ C ∈ 𝓒, ∃ D ∈ 𝓓, E = C ∩ D}

/-- Pairwise union class. -/
def unionClass (𝓒 𝓓 : Set (Set α)) : Set (Set α) :=
  {E | ∃ C ∈ 𝓒, ∃ D ∈ 𝓓, E = C ∪ D}

@[simp] theorem finiteTraceOf_inter (A : Finset α) (C D : Set α) :
    finiteTraceOf A (C ∩ D) = finiteTraceOf A C ∩ finiteTraceOf A D := by
  ext x
  simp [finiteTraceOf]

@[simp] theorem finiteTraceOf_union (A : Finset α) (C D : Set α) :
    finiteTraceOf A (C ∪ D) = finiteTraceOf A C ∪ finiteTraceOf A D := by
  ext x
  simp [finiteTraceOf]

/-- Traces of pairwise intersections lie in the binary image of the trace families. -/
theorem finiteTraceFamily_intersection_subset_image₂
    (𝓒 𝓓 : Set (Set α)) (A : Finset α) :
    finiteTraceFamily (intersectionClass 𝓒 𝓓) A ⊆
      Finset.image₂ (· ∩ ·) (finiteTraceFamily 𝓒 A) (finiteTraceFamily 𝓓 A) := by
  intro B hB
  rw [mem_finiteTraceFamily] at hB
  rcases hB with ⟨E, ⟨C, hC, D, hD, rfl⟩, rfl⟩
  rw [finiteTraceOf_inter]
  exact Finset.mem_image₂_of_mem
    ((mem_finiteTraceFamily 𝓒 A _).2 ⟨C, hC, rfl⟩)
    ((mem_finiteTraceFamily 𝓓 A _).2 ⟨D, hD, rfl⟩)

/-- Traces of pairwise unions lie in the binary image of the trace families. -/
theorem finiteTraceFamily_union_subset_image₂
    (𝓒 𝓓 : Set (Set α)) (A : Finset α) :
    finiteTraceFamily (unionClass 𝓒 𝓓) A ⊆
      Finset.image₂ (· ∪ ·) (finiteTraceFamily 𝓒 A) (finiteTraceFamily 𝓓 A) := by
  intro B hB
  rw [mem_finiteTraceFamily] at hB
  rcases hB with ⟨E, ⟨C, hC, D, hD, rfl⟩, rfl⟩
  rw [finiteTraceOf_union]
  exact Finset.mem_image₂_of_mem
    ((mem_finiteTraceFamily 𝓒 A _).2 ⟨C, hC, rfl⟩)
    ((mem_finiteTraceFamily 𝓓 A _).2 ⟨D, hD, rfl⟩)

/-- Product bound for the number of traces of pairwise intersections. -/
theorem finiteTraceFamily_intersection_card_le
    (𝓒 𝓓 : Set (Set α)) (A : Finset α) :
    (finiteTraceFamily (intersectionClass 𝓒 𝓓) A).card ≤
      (finiteTraceFamily 𝓒 A).card * (finiteTraceFamily 𝓓 A).card := by
  calc
    (finiteTraceFamily (intersectionClass 𝓒 𝓓) A).card
        ≤ (Finset.image₂ (· ∩ ·)
          (finiteTraceFamily 𝓒 A) (finiteTraceFamily 𝓓 A)).card :=
      Finset.card_le_card (finiteTraceFamily_intersection_subset_image₂ 𝓒 𝓓 A)
    _ ≤ (finiteTraceFamily 𝓒 A).card * (finiteTraceFamily 𝓓 A).card :=
      Finset.card_image₂_le _ _ _

/-- Product bound for the number of traces of pairwise unions. -/
theorem finiteTraceFamily_union_card_le
    (𝓒 𝓓 : Set (Set α)) (A : Finset α) :
    (finiteTraceFamily (unionClass 𝓒 𝓓) A).card ≤
      (finiteTraceFamily 𝓒 A).card * (finiteTraceFamily 𝓓 A).card := by
  calc
    (finiteTraceFamily (unionClass 𝓒 𝓓) A).card
        ≤ (Finset.image₂ (· ∪ ·)
          (finiteTraceFamily 𝓒 A) (finiteTraceFamily 𝓓 A)).card :=
      Finset.card_le_card (finiteTraceFamily_union_subset_image₂ 𝓒 𝓓 A)
    _ ≤ (finiteTraceFamily 𝓒 A).card * (finiteTraceFamily 𝓓 A).card :=
      Finset.card_image₂_le _ _ _

end Chapter03
end InfiniteDimensionalStatistics
