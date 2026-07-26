/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.OuterLawPermanence

/-!
# Chapter 3: Local-class permanence

Monotonicity of difference and localised difference classes in the underlying
function class and in the localisation radius.  No monotonicity claim is made
for internal covering numbers without additional metric hypotheses.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section DifferenceClasses

variable {S : Type*} [MeasurableSpace S]
variable {𝓕 𝓖 : Set (S → ℝ)}

/-- Difference classes are monotone in the underlying class. -/
theorem differenceClass_mono (h𝓖𝓕 : 𝓖 ⊆ 𝓕) :
    differenceClass 𝓖 ⊆ differenceClass 𝓕 := by
  intro h hh
  rcases hh with ⟨f, hf, g, hg, rfl⟩
  exact ⟨f, h𝓖𝓕 hf, g, h𝓖𝓕 hg, rfl⟩

/-- Population-local difference classes are monotone in the underlying class. -/
theorem populationLocalDifferenceClass_mono_class
    (P : Measure S) (δ : ℝ) (h𝓖𝓕 : 𝓖 ⊆ 𝓕) :
    populationLocalDifferenceClass P 𝓖 δ ⊆
      populationLocalDifferenceClass P 𝓕 δ := by
  intro h hh
  exact ⟨differenceClass_mono h𝓖𝓕 hh.1, hh.2⟩

/-- Population-local difference classes increase with their radius. -/
theorem populationLocalDifferenceClass_mono_radius
    (P : Measure S) (𝓕 : Set (S → ℝ)) {δ δ' : ℝ} (hδ : δ ≤ δ') :
    populationLocalDifferenceClass P 𝓕 δ ⊆
      populationLocalDifferenceClass P 𝓕 δ' := by
  intro h hh
  exact ⟨hh.1, hh.2.trans hδ⟩

/-- The corrected Donsker-local class is monotone in the underlying class. -/
theorem donskerLocalDifferenceClass_mono_class
    (P : Measure S) (ε : ℝ) (n : ℕ) (h𝓖𝓕 : 𝓖 ⊆ 𝓕) :
    donskerLocalDifferenceClass P 𝓖 ε n ⊆
      donskerLocalDifferenceClass P 𝓕 ε n := by
  simpa [donskerLocalDifferenceClass] using
    populationLocalDifferenceClass_mono_class P
      (ε / Real.sqrt (n : ℝ)) h𝓖𝓕

/-- Empirical `L²` local classes are monotone in the underlying class. -/
theorem empiricalL2LocalDifferenceClass_mono_class {n : ℕ}
    (X : Fin n → S) (δ : ℝ) (h𝓖𝓕 : 𝓖 ⊆ 𝓕) :
    empiricalL2LocalDifferenceClass X 𝓖 δ ⊆
      empiricalL2LocalDifferenceClass X 𝓕 δ := by
  intro h hh
  exact ⟨differenceClass_mono h𝓖𝓕 hh.1, hh.2⟩

/-- Empirical `L²` local classes increase with their radius. -/
theorem empiricalL2LocalDifferenceClass_mono_radius {n : ℕ}
    (X : Fin n → S) (𝓕 : Set (S → ℝ)) {δ δ' : ℝ} (hδ : δ ≤ δ') :
    empiricalL2LocalDifferenceClass X 𝓕 δ ⊆
      empiricalL2LocalDifferenceClass X 𝓕 δ' := by
  intro h hh
  exact ⟨hh.1, hh.2.trans hδ⟩

/-- Empirical `L¹` local classes are monotone in the underlying class. -/
theorem empiricalL1LocalDifferenceClass_mono_class {n : ℕ}
    (X : Fin n → S) (δ : ℝ) (h𝓖𝓕 : 𝓖 ⊆ 𝓕) :
    empiricalL1LocalDifferenceClass X 𝓖 δ ⊆
      empiricalL1LocalDifferenceClass X 𝓕 δ := by
  intro h hh
  exact ⟨differenceClass_mono h𝓖𝓕 hh.1, hh.2⟩

/-- Empirical `L¹` local classes increase with their radius. -/
theorem empiricalL1LocalDifferenceClass_mono_radius {n : ℕ}
    (X : Fin n → S) (𝓕 : Set (S → ℝ)) {δ δ' : ℝ} (hδ : δ ≤ δ') :
    empiricalL1LocalDifferenceClass X 𝓕 δ ⊆
      empiricalL1LocalDifferenceClass X 𝓕 δ' := by
  intro h hh
  exact ⟨hh.1, hh.2.trans hδ⟩

end DifferenceClasses

end Chapter03
end InfiniteDimensionalStatistics
