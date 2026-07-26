/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.EquicontinuityPermanence
import InfiniteDimensionalStatistics.Chapter03.OuterMeasureLemmas

/-!
# Chapter 3: Glivenko–Cantelli permanence

Uniform empirical deviations decrease when the indexing class is restricted.
Consequently both almost-sure and weak outer-probability Glivenko–Cantelli
properties pass to subclasses.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section UniformDeviation

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
variable {𝓕 𝓖 : Set (S → ℝ)}

/-- Restricting the function class can only decrease uniform empirical deviation. -/
theorem uniformEmpiricalDeviation_mono {n : ℕ}
    (P : Measure S) (X : Fin n → S) (h𝓖𝓕 : 𝓖 ⊆ 𝓕) :
    uniformEmpiricalDeviation P X 𝓖 ≤ uniformEmpiricalDeviation P X 𝓕 := by
  unfold uniformEmpiricalDeviation
  refine iSup_le fun g => ?_
  exact le_iSup_of_le (⟨g.1, h𝓖𝓕 g.2⟩ : 𝓕) (by rfl)

/-- The pathwise uniform deviation is monotone in the indexing class. -/
theorem samplePathUniformDeviation_mono
    (P : Measure S) (X : ℕ → Ω → S) (h𝓖𝓕 : 𝓖 ⊆ 𝓕)
    (n : ℕ) (ω : Ω) :
    samplePathUniformDeviation P 𝓖 X n ω ≤
      samplePathUniformDeviation P 𝓕 X n ω := by
  exact uniformEmpiricalDeviation_mono P
    (samplePrefix (fun i => X i ω) n) h𝓖𝓕

/-- The almost-sure Glivenko–Cantelli property passes to subclasses. -/
theorem IsGlivenkoCantelli.mono
    (sampleMeasure : Measure Ω) (P : Measure S) (X : ℕ → Ω → S)
    (h𝓕 : IsGlivenkoCantelli sampleMeasure P 𝓕 X)
    (h𝓖𝓕 : 𝓖 ⊆ 𝓕) :
    IsGlivenkoCantelli sampleMeasure P 𝓖 X := by
  filter_upwards [h𝓕] with ω hω
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hω
    (fun _ => bot_le)
    (fun n => samplePathUniformDeviation_mono P X h𝓖𝓕 n ω)

/-- The weak outer-probability Glivenko–Cantelli property passes to subclasses. -/
theorem IsWeakGlivenkoCantelli.mono
    (sampleMeasure : Measure Ω) (P : Measure S) (X : ℕ → Ω → S)
    (h𝓕 : IsWeakGlivenkoCantelli sampleMeasure P 𝓕 X)
    (h𝓖𝓕 : 𝓖 ⊆ 𝓕) :
    IsWeakGlivenkoCantelli sampleMeasure P 𝓖 X := by
  intro ε hε
  have hlarge := h𝓕 ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hlarge
    (fun _ => bot_le)
    (fun n => outerProbability_mono sampleMeasure <| by
      intro ω hω
      exact hω.trans_le (samplePathUniformDeviation_mono P X h𝓖𝓕 n ω))

end UniformDeviation

end Chapter03
end InfiniteDimensionalStatistics
