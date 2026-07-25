/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.InterfaceLemmas
import Mathlib.Combinatorics.SetFamily.Shatter

/-!
# Chapter 3: Finite traces and Sauer–Shelah

An adapter from arbitrary set classes traced on a finite set to Mathlib's
finite set-family API.  The cardinal estimate is Mathlib's proved
Sauer–Shelah lemma.
-/

noncomputable section

open scoped BigOperators
open Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section FiniteTrace

variable {α : Type*}

/-- Trace of a set on the finite subtype determined by `A`. -/
def finiteTraceOf (A : Finset α) (C : Set α) : Finset A :=
  Finset.univ.filter fun x ↦ x.1 ∈ C

/-- The finite family of all traces of `𝓒` on `A`. -/
def finiteTraceFamily (𝓒 : Set (Set α)) (A : Finset α) :
    Finset (Finset A) :=
  Finset.univ.filter fun B ↦ ∃ C ∈ 𝓒, B = finiteTraceOf A C

@[simp] theorem mem_finiteTraceFamily
    (𝓒 : Set (Set α)) (A : Finset α) (B : Finset A) :
    B ∈ finiteTraceFamily 𝓒 A ↔ ∃ C ∈ 𝓒, B = finiteTraceOf A C := by
  simp [finiteTraceFamily]

/-- Every trace is a subset of the finite ambient subtype. -/
theorem finiteTraceOf_subset_univ (A : Finset α) (C : Set α) :
    finiteTraceOf A C ⊆ Finset.univ :=
  fun _ _ ↦ Finset.mem_univ _

/--
Finite Sauer–Shelah estimate for the trace family.

Source: Theorem 3.6.2, printed pp. 212–214; specification id
`theorem_3_6_2`.  This theorem uses Mathlib's convention where `vcDim` is the
largest shattered cardinality; the book's VC index is one larger.
-/
theorem finiteTraceFamily_card_le_sauerShelah
    (𝓒 : Set (Set α)) (A : Finset α) :
    (finiteTraceFamily 𝓒 A).card ≤
      ∑ k ∈ Finset.Iic (finiteTraceFamily 𝓒 A).vcDim,
        A.card.choose k := by
  calc
    (finiteTraceFamily 𝓒 A).card
        ≤ (finiteTraceFamily 𝓒 A).shatterer.card :=
      Finset.card_le_card_shatterer _
    _ ≤ ∑ k ∈ Finset.Iic (finiteTraceFamily 𝓒 A).vcDim,
        (Fintype.card A).choose k :=
      Finset.card_shatterer_le_sum_vcDim
    _ = ∑ k ∈ Finset.Iic (finiteTraceFamily 𝓒 A).vcDim,
        A.card.choose k := by
      simp

/-- The trace family has at most all subsets of the sample. -/
theorem finiteTraceFamily_card_le_two_pow
    (𝓒 : Set (Set α)) (A : Finset α) :
    (finiteTraceFamily 𝓒 A).card ≤ 2 ^ A.card := by
  calc
    (finiteTraceFamily 𝓒 A).card ≤ (Finset.univ : Finset (Finset A)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ A.card := by simp

end FiniteTrace

end Chapter03
end InfiniteDimensionalStatistics
