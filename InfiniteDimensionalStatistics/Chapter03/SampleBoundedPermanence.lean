/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.ConvexClosurePermanence

/-!
# Chapter 3: Sample-boundedness permanence

A reindexed subprocess has path supremum at most that of the original process.
Consequently sample boundedness is inherited by every subprocess.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Reindexing

variable {T U Ω : Type*} [MeasurableSpace Ω]

/-- Reindexing can only decrease the extended sample-path supremum. -/
theorem sampleSupNorm_comp_le
    (X : RealProcess T Ω) (ι : U → T) (ω : Ω) :
    sampleSupNorm (fun u => X (ι u)) ω ≤ sampleSupNorm X ω := by
  unfold sampleSupNorm
  exact iSup_le fun u => le_iSup (fun t : T => ENNReal.ofReal |X t ω|) (ι u)

/-- Every reindexed subprocess of a sample-bounded process is sample bounded. -/
theorem IsSampleBounded.comp
    (P : Measure Ω) (X : RealProcess T Ω)
    (hX : IsSampleBounded P X) (ι : U → T) :
    IsSampleBounded P (fun u => X (ι u)) := by
  filter_upwards [hX] with ω hω
  exact (sampleSupNorm_comp_le X ι ω).trans_lt hω

end Reindexing

end Chapter03
end InfiniteDimensionalStatistics
