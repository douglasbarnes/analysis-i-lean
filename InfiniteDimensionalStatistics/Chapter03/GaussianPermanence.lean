/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.GaussianBridge

/-!
# Chapter 3: Gaussian-process permanence

Restriction of the Gaussian bridge, Gaussian motion, path-regularity and
pre-Gaussian realisation predicates to a smaller indexing class.  These are
structural permanence results: the restricted process is obtained by composing
with the subtype inclusion.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Restriction

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
variable {𝓕 𝓖 : Set (S → ℝ)}

/-- Restrict a process indexed by `𝓕` to a subclass `𝓖 ⊆ 𝓕`. -/
def restrictIndexedProcess (h𝓖𝓕 : 𝓖 ⊆ 𝓕) (G : 𝓕 → Ω → ℝ) : 𝓖 → Ω → ℝ :=
  G ∘ fun g : 𝓖 => (⟨g.1, h𝓖𝓕 g.2⟩ : 𝓕)

/-- A Brownian bridge remains a Brownian bridge after restricting its index class. -/
theorem IsBrownianBridge.restrict
    {P : Measure S} {Q : Measure Ω} {G : 𝓕 → Ω → ℝ}
    (hG : IsBrownianBridge P 𝓕 Q G) (h𝓖𝓕 : 𝓖 ⊆ 𝓕) :
    IsBrownianBridge P 𝓖 Q (restrictIndexedProcess h𝓖𝓕 G) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [restrictIndexedProcess] using
      hG.1.comp_right (fun g : 𝓖 => (⟨g.1, h𝓖𝓕 g.2⟩ : 𝓕))
  · intro f
    simpa [restrictIndexedProcess] using
      hG.2.1 (⟨f.1, h𝓖𝓕 f.2⟩ : 𝓕)
  · intro f g
    simpa [restrictIndexedProcess] using
      hG.2.2 (⟨f.1, h𝓖𝓕 f.2⟩ : 𝓕) (⟨g.1, h𝓖𝓕 g.2⟩ : 𝓕)

/-- A Brownian motion indexed by functions remains one after restriction. -/
theorem IsBrownianMotionIndexedBy.restrict
    {P : Measure S} {Q : Measure Ω} {Z : 𝓕 → Ω → ℝ}
    (hZ : IsBrownianMotionIndexedBy P 𝓕 Q Z) (h𝓖𝓕 : 𝓖 ⊆ 𝓕) :
    IsBrownianMotionIndexedBy P 𝓖 Q (restrictIndexedProcess h𝓖𝓕 Z) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [restrictIndexedProcess] using
      hZ.1.comp_right (fun g : 𝓖 => (⟨g.1, h𝓖𝓕 g.2⟩ : 𝓕))
  · intro f
    simpa [restrictIndexedProcess] using
      hZ.2.1 (⟨f.1, h𝓖𝓕 f.2⟩ : 𝓕)
  · intro f g
    simpa [restrictIndexedProcess] using
      hZ.2.2 (⟨f.1, h𝓖𝓕 f.2⟩ : 𝓕) (⟨g.1, h𝓖𝓕 g.2⟩ : 𝓕)

/-- Bounded uniformly continuous sample paths are preserved by reindexing. -/
theorem HasBoundedUniformlyContinuousPaths.comp
    {T U : Type*} {Q : Measure Ω} {d : T → T → ℝ}
    {G : T → Ω → ℝ} (hG : HasBoundedUniformlyContinuousPaths Q d G)
    (ι : U → T) :
    HasBoundedUniformlyContinuousPaths Q
      (fun s t => d (ι s) (ι t)) (G ∘ ι) := by
  filter_upwards [hG] with ω hω
  constructor
  · rcases hω.1 with ⟨M, hM⟩
    exact ⟨M, fun u => hM (ι u)⟩
  · intro ε hε
    rcases hω.2 ε hε with ⟨δ, hδ, hcont⟩
    exact ⟨δ, hδ, fun s t hst => hcont (ι s) (ι t) hst⟩

/-- A concrete pre-Gaussian realisation restricts to every subclass. -/
theorem RealisesPreGaussianClass.restrict
    {P : Measure S} {Q : Measure Ω} {G : 𝓕 → Ω → ℝ}
    (hG : RealisesPreGaussianClass P 𝓕 Q G) (h𝓖𝓕 : 𝓖 ⊆ 𝓕) :
    RealisesPreGaussianClass P 𝓖 Q (restrictIndexedProcess h𝓖𝓕 G) := by
  refine ⟨hG.1.restrict h𝓖𝓕, ?_⟩
  simpa [restrictIndexedProcess] using
    hG.2.comp (fun g : 𝓖 => (⟨g.1, h𝓖𝓕 g.2⟩ : 𝓕))

end Restriction

end Chapter03
end InfiniteDimensionalStatistics
