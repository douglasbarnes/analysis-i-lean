/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.OuterLaw

/-!
# Chapter 3: Elementary outer-measure calculus

Order-theoretic facts used by Propositions 3.7.1–3.7.2.  The clauses whose
exact source formulation is still marked as page-image-sensitive are not
invented here.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section OuterProbability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Outer probability is monotone. -/
theorem outerProbability_mono (P : Measure Ω) {A B : Set Ω}
    (hAB : A ⊆ B) :
    outerProbability P A ≤ outerProbability P B := by
  exact measure_mono hAB

/-- Outer probability is finitely subadditive. -/
theorem outerProbability_union_le (P : Measure Ω) (A B : Set Ω) :
    outerProbability P (A ∪ B) ≤
      outerProbability P A + outerProbability P B := by
  exact measure_union_le A B

/-- The outer probability of the whole space is the total mass. -/
@[simp] theorem outerProbability_univ (P : Measure Ω) :
    outerProbability P Set.univ = P Set.univ := by
  rfl

/-- On measurable sets, the outer-probability notation is the ordinary measure. -/
theorem outerProbability_eq_measure (P : Measure Ω) (A : Set Ω)
    (_hA : MeasurableSet A) :
    outerProbability P A = P A := by
  rfl

end OuterProbability

section NonnegativeOuterExpectation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Any measurable majorant bounds the outer expectation from above. -/
theorem outerExpectation_le_lintegral_majorant
    (P : Measure Ω) {X Y : Ω → ℝ≥0∞}
    (hY : Measurable Y) (hXY : X ≤ Y) :
    outerExpectation P X ≤ ∫⁻ ω, Y ω ∂P := by
  unfold outerExpectation
  exact iInf_le_of_le Y
    (iInf_le_of_le hY
      (iInf_le_of_le hXY le_rfl))

/-- Outer expectation is monotone. -/
theorem outerExpectation_mono
    (P : Measure Ω) {X Y : Ω → ℝ≥0∞}
    (hXY : X ≤ Y) :
    outerExpectation P X ≤ outerExpectation P Y := by
  unfold outerExpectation
  refine le_iInf fun Z ↦ ?_
  refine le_iInf fun hZ ↦ ?_
  refine le_iInf fun hYZ ↦ ?_
  exact iInf_le_of_le Z
    (iInf_le_of_le hZ
      (iInf_le_of_le (hXY.trans hYZ) le_rfl))

/-- For a measurable nonnegative function, outer expectation equals its integral. -/
theorem outerExpectation_eq_lintegral
    (P : Measure Ω) (X : Ω → ℝ≥0∞) (hX : Measurable X) :
    outerExpectation P X = ∫⁻ ω, X ω ∂P := by
  apply le_antisymm
  · exact outerExpectation_le_lintegral_majorant P hX le_rfl
  · unfold outerExpectation
    refine le_iInf fun Y ↦ ?_
    refine le_iInf fun _hY ↦ ?_
    refine le_iInf fun hXY ↦ ?_
    exact lintegral_mono hXY

/-- The outer expectation of the zero function is zero. -/
@[simp] theorem outerExpectation_zero (P : Measure Ω) :
    outerExpectation P (fun _ ↦ 0) = 0 := by
  rw [outerExpectation_eq_lintegral P _ measurable_const]
  simp

end NonnegativeOuterExpectation

section MeasurableCovers

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable cover is itself a measurable majorant. -/
theorem IsMeasurableCover.measurable
    (P : Measure Ω) {f fstar : Ω → ℝ}
    (h : IsMeasurableCover P f fstar) : Measurable fstar :=
  h.1.1

/-- A measurable cover pointwise majorises the original function. -/
theorem IsMeasurableCover.le
    (P : Measure Ω) {f fstar : Ω → ℝ}
    (h : IsMeasurableCover P f fstar) : f ≤ fstar :=
  h.1.2

/-- Two measurable covers of the same function agree almost everywhere. -/
theorem IsMeasurableCover.ae_eq
    (P : Measure Ω) {f fstar gstar : Ω → ℝ}
    (hf : IsMeasurableCover P f fstar)
    (hg : IsMeasurableCover P f gstar) :
    fstar =ᵐ[P] gstar := by
  exact Filter.EventuallyLE.antisymm
    (hf.2 gstar hg.1)
    (hg.2 fstar hf.1)

end MeasurableCovers

end Chapter03
end InfiniteDimensionalStatistics
