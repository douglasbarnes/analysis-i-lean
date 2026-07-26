/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.PrelinearityLemmas
import InfiniteDimensionalStatistics.Chapter03.InterfaceLemmas

/-!
# Chapter 3: Hull and sequential-closure permanence

Monotonicity of the elementary class hulls and of the symmetric convex
pointwise/`L²(P)` sequential closure `H(𝓕,P)`.  This is the set-theoretic core
used by the later Donsker convex-hull permanence theorem.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Hulls

variable {S : Type*} [MeasurableSpace S]
variable {𝓕 𝓖 : Set (S → ℝ)}

/-- Scalar images are monotone in the underlying class. -/
theorem scalarClass_mono (a : ℝ) (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    scalarClass a 𝓕 ⊆ scalarClass a 𝓖 := by
  rintro g ⟨f, hf, rfl⟩
  exact ⟨f, h𝓕𝓖 hf, rfl⟩

/-- Symmetric hulls are monotone in the underlying class. -/
theorem symmetricHull_mono (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    symmetricHull 𝓕 ⊆ symmetricHull 𝓖 := by
  intro f hf
  rcases hf with hf | ⟨g, hg, rfl⟩
  · exact Or.inl (h𝓕𝓖 hf)
  · exact Or.inr ⟨g, h𝓕𝓖 hg, rfl⟩

/-- Star hulls are monotone in the underlying class. -/
theorem starHull_mono (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    starHull 𝓕 ⊆ starHull 𝓖 := by
  rintro g ⟨a, ha, f, hf, rfl⟩
  exact ⟨a, ha, f, h𝓕𝓖 hf, rfl⟩

/-- Pointwise composition images are monotone in the underlying class. -/
theorem compositionClass_mono (φ : ℝ → ℝ) (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    compositionClass φ 𝓕 ⊆ compositionClass φ 𝓖 := by
  rintro g ⟨f, hf, rfl⟩
  exact ⟨f, h𝓕𝓖 hf, rfl⟩

/-- Symmetric convex hulls are monotone in the underlying class. -/
theorem symmetricConvexHull_mono (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    symmetricConvexHull 𝓕 ⊆ symmetricConvexHull 𝓖 := by
  unfold symmetricConvexHull
  exact convexHull_mono (symmetricHull_mono h𝓕𝓖)

end Hulls

section SequentialClosure

variable {S : Type*} [MeasurableSpace S]
variable {𝓕 𝓖 : Set (S → ℝ)} {f : S → ℝ}

/-- Membership in `H(𝓕,P)` is monotone in the underlying class. -/
theorem InSymmetricConvexSequentialClosure.mono
    (P : Measure S) (h𝓕𝓖 : 𝓕 ⊆ 𝓖)
    (hf : InSymmetricConvexSequentialClosure P 𝓕 f) :
    InSymmetricConvexSequentialClosure P 𝓖 f := by
  rcases hf with ⟨u, hu, hpoint, hL2⟩
  exact ⟨u, fun n => symmetricConvexHull_mono h𝓕𝓖 (hu n), hpoint, hL2⟩

/-- The sequential closure `H(𝓕,P)` is monotone in `𝓕`. -/
theorem symmetricConvexSequentialClosure_mono
    (P : Measure S) (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    symmetricConvexSequentialClosure P 𝓕 ⊆
      symmetricConvexSequentialClosure P 𝓖 := by
  intro f hf
  exact hf.mono P h𝓕𝓖

/-- Every member of the symmetric convex hull lies in its constant sequential closure. -/
theorem symmetricConvexHull_subset_symmetricConvexSequentialClosure
    (P : Measure S) (𝓕 : Set (S → ℝ)) :
    symmetricConvexHull 𝓕 ⊆ symmetricConvexSequentialClosure P 𝓕 := by
  intro f hf
  refine ⟨fun _ => f, fun _ => hf, ?_, ?_⟩
  · intro x
    exact tendsto_const_nhds
  · simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Every original class is contained in `H(𝓕,P)`. -/
theorem subset_symmetricConvexSequentialClosure
    (P : Measure S) (𝓕 : Set (S → ℝ)) :
    𝓕 ⊆ symmetricConvexSequentialClosure P 𝓕 :=
  (subset_symmetricConvexHull 𝓕).trans
    (symmetricConvexHull_subset_symmetricConvexSequentialClosure P 𝓕)

end SequentialClosure

end Chapter03
end InfiniteDimensionalStatistics
