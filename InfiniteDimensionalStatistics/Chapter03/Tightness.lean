/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.MeasurableWeakConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Chapter 3: Tightness and Prokhorov compactness

Measurable probability-measure compactness results reused from Mathlib's
Prokhorov theorem.  Outer asymptotic tightness of nonmeasurable random maps
remains a separate notion in `OuterLaw.lean`.
-/

noncomputable section

open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section TightMeasureFamilies

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [T2Space E] [BorelSpace E]

/-- Tightness of a set of probability measures. -/
def IsTightProbabilityMeasureSet (S : Set (ProbabilityMeasure E)) : Prop :=
  IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}

/--
Prokhorov compactness: the closure of a tight family of probability measures is
compact.
-/
theorem compact_closure_of_tight_probabilityMeasures
    {S : Set (ProbabilityMeasure E)}
    (hS : IsTightProbabilityMeasureSet S) :
    IsCompact (closure S) :=
  isCompact_closure_of_isTightMeasureSet hS

/-- A tight family is relatively compact. -/
theorem relativelyCompact_of_tight_probabilityMeasures
    {S : Set (ProbabilityMeasure E)}
    (hS : IsTightProbabilityMeasureSet S) :
    IsCompact (closure S) :=
  compact_closure_of_tight_probabilityMeasures hS

end TightMeasureFamilies

section QuantitativeCompactness

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [T2Space E] [BorelSpace E]

/--
Compactness of probability measures satisfying a sequence of compact-tail
bounds.
-/
theorem compact_probabilityMeasures_with_compact_tail_bounds
    {u : ℕ → ℝ≥0} {K : ℕ → Set E}
    (hu : Tendsto u atTop (𝓝 0))
    (hK : ∀ n, IsCompact (K n))
    (hregularity : NormalSpace E ∨ Monotone K) :
    IsCompact {μ : ProbabilityMeasure E | ∀ n, μ (K n)ᶜ ≤ u n} :=
  isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
    hu hK hregularity

end QuantitativeCompactness

end Chapter03
end InfiniteDimensionalStatistics
