/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.GaussianPermanence

/-!
# Chapter 3: Equicontinuity permanence

Restriction of increment suprema and asymptotic equicontinuity to a smaller
indexing set.  The restricted increment supremum is bounded by the original
one, so every outer-probability equicontinuity estimate is inherited.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section IncrementSupremum

variable {T U Ω : Type*} [MeasurableSpace Ω]

/-- Reindexing a process can only decrease its increment supremum. -/
theorem processIncrementSupremum_comp_le
    (d : T → T → ℝ) (X : T → Ω → ℝ) (ι : U → T)
    (δ : ℝ) (ω : Ω) :
    processIncrementSupremum (fun s t => d (ι s) (ι t))
        (fun u => X (ι u)) δ ω ≤
      processIncrementSupremum d X δ ω := by
  unfold processIncrementSupremum
  refine iSup_le fun s => iSup_le fun t => ?_
  exact le_iSup_of_le (ι s) <| le_iSup_of_le (ι t) <| by rfl

/-- Asymptotic equicontinuity is inherited by every reindexed subprocess. -/
theorem AsymptoticallyEquicontinuous.comp
    (P : ℕ → Measure Ω) (d : T → T → ℝ)
    (X : ℕ → T → Ω → ℝ) (ι : U → T)
    (hX : AsymptoticallyEquicontinuous P d X) :
    AsymptoticallyEquicontinuous P
      (fun s t => d (ι s) (ι t))
      (fun n u => X n (ι u)) := by
  intro ε hε η hη
  rcases hX ε hε η hη with ⟨δ, hδ, N, hN⟩
  refine ⟨δ, hδ, N, fun n hn => ?_⟩
  calc
    P n {ω | ENNReal.ofReal ε <
        processIncrementSupremum (fun s t => d (ι s) (ι t))
          (fun u => X n (ι u)) δ ω} ≤
      P n {ω | ENNReal.ofReal ε < processIncrementSupremum d (X n) δ ω} := by
        apply measure_mono
        intro ω hω
        exact hω.trans_le (processIncrementSupremum_comp_le d (X n) ι δ ω)
    _ ≤ ENNReal.ofReal η := hN n hn

end IncrementSupremum

end Chapter03
end InfiniteDimensionalStatistics
