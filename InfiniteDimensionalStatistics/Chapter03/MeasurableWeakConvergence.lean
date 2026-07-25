/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.FiniteClassGlivenkoCantelli
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Chapter 3: Measurable weak convergence

The ordinary Borel-measurable special case of the Chapter 3 weak-convergence
machinery.  The outer-law extension for nonmeasurable random maps remains in
`OuterLaw.lean`.
-/

noncomputable section

open scoped Topology ENNReal NNReal BoundedContinuousFunction
open MeasureTheory Filter Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section FiniteMeasures

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [OpensMeasurableSpace E]

/-- Weak convergence in Mathlib's topology on finite measures. -/
def FiniteMeasuresWeaklyConverge
    (μn : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) : Prop :=
  Tendsto μn atTop (𝓝 μ)

/-- Bounded-continuous integral characterization of finite-measure convergence. -/
theorem finiteMeasuresWeaklyConverge_iff_integrals
    (μn : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) :
    FiniteMeasuresWeaklyConverge μn μ ↔
      ∀ f : E →ᵇ ℝ,
        Tendsto
          (fun n ↦ ∫ x, f x ∂(μn n : Measure E))
          atTop
          (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto

end FiniteMeasures

section ProbabilityMeasures

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [OpensMeasurableSpace E] [HasOuterApproxClosed E]

/-- Weak convergence in Mathlib's topology on probability measures. -/
def ProbabilityMeasuresWeaklyConverge
    (μn : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E) : Prop :=
  Tendsto μn atTop (𝓝 μ)

/-- Portmanteau closed-set upper bound. -/
theorem weakConvergence_limsup_closed
    {μn : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (h : ProbabilityMeasuresWeaklyConverge μn μ)
    {F : Set E} (hF : IsClosed F) :
    (atTop.limsup fun n ↦ (μn n : Measure E) F) ≤
      (μ : Measure E) F :=
  ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hF

/-- Portmanteau open-set lower bound. -/
theorem weakConvergence_liminf_open
    {μn : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (h : ProbabilityMeasuresWeaklyConverge μn μ)
    {G : Set E} (hG : IsOpen G) :
    (μ : Measure E) G ≤
      atTop.liminf (fun n ↦ (μn n : Measure E) G) :=
  ProbabilityMeasure.le_liminf_measure_open_of_tendsto h hG

/-- Convergence on Borel sets whose frontier has zero limit mass. -/
theorem weakConvergence_tendsto_measure_null_frontier
    {μn : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (h : ProbabilityMeasuresWeaklyConverge μn μ)
    {A : Set E} (hA : (μ : Measure E) (frontier A) = 0) :
    Tendsto (fun n ↦ (μn n : Measure E) A) atTop
      (𝓝 ((μ : Measure E) A)) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hA

end ProbabilityMeasures

end Chapter03
end InfiniteDimensionalStatistics
