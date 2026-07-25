/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.BridgeCovarianceLemmas

/-!
# Chapter 3: Elementary metric-entropy lemmas

Finite-net and separated-set facts used before the analytical chaining bounds.
-/

noncomputable section

open Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

variable {α : Type*}

/-- An epsilon net remains a net when the radius is enlarged. -/
theorem IsEpsilonNet.mono_radius
    {d : α → α → ℝ} {A C : Set α} {ε δ : ℝ}
    (h : IsEpsilonNet d A C ε) (hεδ : ε ≤ δ) :
    IsEpsilonNet d A C δ := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro x hx
  rcases h.2.2 x hx with ⟨y, hyC, hxy⟩
  exact ⟨y, hyC, hxy.trans hεδ⟩

/-- An epsilon-separated set remains separated when the threshold is decreased. -/
theorem IsEpsilonSeparated.mono_radius
    {d : α → α → ℝ} {A C : Set α} {ε δ : ℝ}
    (h : IsEpsilonSeparated d A C ε) (hδε : δ ≤ ε) :
    IsEpsilonSeparated d A C δ := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro x hx y hy hxy
  exact lt_of_le_of_lt hδε (h.2.2 hx hy hxy)

/-- A finite set covers itself at every nonnegative radius when the diagonal distance is zero. -/
theorem finite_isEpsilonNet_self
    (d : α → α → ℝ) (A : Set α) (hA : A.Finite)
    (hdiag : ∀ x, d x x = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    IsEpsilonNet d A A ε := by
  refine ⟨hA, Subset.rfl, ?_⟩
  intro x hx
  exact ⟨x, hx, by simpa [hdiag x] using hε⟩

/-- A finite self-cover gives an explicit upper bound on the covering number. -/
theorem coveringNumber_le_ncard
    (d : α → α → ℝ) (A : Set α) (hA : A.Finite)
    (hdiag : ∀ x, d x x = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    coveringNumber d A ε ≤ (A.ncard : WithTop ℕ) := by
  unfold coveringNumber
  apply sInf_le
  exact ⟨A, finite_isEpsilonNet_self d A hA hdiag hε, rfl⟩

/-- Every finite separated witness gives a lower bound on the packing number. -/
theorem ncard_le_packingNumber
    (d : α → α → ℝ) (A C : Set α) {ε : ℝ}
    (hC : IsEpsilonSeparated d A C ε) :
    (C.ncard : WithTop ℕ) ≤ packingNumber d A ε := by
  unfold packingNumber
  apply le_sSup
  exact ⟨C, hC, rfl⟩

/-- The empty set has covering number zero. -/
theorem coveringNumber_empty (d : α → α → ℝ) (ε : ℝ) :
    coveringNumber d ∅ ε = 0 := by
  apply le_antisymm
  · unfold coveringNumber
    apply sInf_le
    refine ⟨∅, ?_, by simp⟩
    exact ⟨Set.finite_empty, Subset.rfl, by simp⟩
  · exact bot_le

/-- A singleton has covering number at most one at every nonnegative radius. -/
theorem coveringNumber_singleton_le_one
    (d : α → α → ℝ) (x : α) (hdiag : d x x = 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    coveringNumber d {x} ε ≤ 1 := by
  simpa using coveringNumber_le_ncard d {x} (Set.finite_singleton x)
    (fun y ↦ by simpa using hdiag) hε

end Chapter03
end InfiniteDimensionalStatistics
