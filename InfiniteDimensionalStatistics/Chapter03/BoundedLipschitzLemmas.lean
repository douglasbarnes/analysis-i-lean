/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.SymmetryLemmas

/-!
# Chapter 3: Bounded-Lipschitz discrepancy lemmas

Nonnegativity, symmetry and the triangle inequality for the extended
bounded-Lipschitz discrepancy used to encode measurable weak convergence.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section BoundedLipschitzDistance

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

/-- Bounded-Lipschitz distance is nonnegative. -/
theorem boundedLipschitzDistance_nonneg (P Q : Measure E) :
    0 ≤ boundedLipschitzDistance P Q :=
  bot_le

/-- Bounded-Lipschitz distance is symmetric. -/
theorem boundedLipschitzDistance_comm (P Q : Measure E) :
    boundedLipschitzDistance P Q = boundedLipschitzDistance Q P := by
  apply le_antisymm
  · unfold boundedLipschitzDistance
    refine iSup_le fun f => ?_
    exact le_iSup_of_le f (by rw [abs_sub_comm])
  · unfold boundedLipschitzDistance
    refine iSup_le fun f => ?_
    exact le_iSup_of_le f (by rw [abs_sub_comm])

/-- Bounded-Lipschitz distance satisfies the triangle inequality. -/
theorem boundedLipschitzDistance_triangle
    (P Q R : Measure E) :
    boundedLipschitzDistance P R ≤
      boundedLipschitzDistance P Q + boundedLipschitzDistance Q R := by
  unfold boundedLipschitzDistance
  refine iSup_le fun f => ?_
  let p := ∫ x, f.1 x ∂P
  let q := ∫ x, f.1 x ∂Q
  let r := ∫ x, f.1 x ∂R
  calc
    ENNReal.ofReal |p - r| ≤
        ENNReal.ofReal (|p - q| + |q - r|) :=
      ENNReal.ofReal_le_ofReal (abs_sub_le p q r)
    _ = ENNReal.ofReal |p - q| + ENNReal.ofReal |q - r| :=
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤
        (⨆ g : boundedLipschitzClass (E := E),
          ENNReal.ofReal
            |(∫ x, g.1 x ∂P) - ∫ x, g.1 x ∂Q|) +
        (⨆ g : boundedLipschitzClass (E := E),
          ENNReal.ofReal
            |(∫ x, g.1 x ∂Q) - ∫ x, g.1 x ∂R|) := by
      apply add_le_add
      · exact le_iSup (fun g : boundedLipschitzClass (E := E) =>
          ENNReal.ofReal |(∫ x, g.1 x ∂P) - ∫ x, g.1 x ∂Q|) f
      · exact le_iSup (fun g : boundedLipschitzClass (E := E) =>
          ENNReal.ofReal |(∫ x, g.1 x ∂Q) - ∫ x, g.1 x ∂R|) f

end BoundedLipschitzDistance

end Chapter03
end InfiniteDimensionalStatistics
