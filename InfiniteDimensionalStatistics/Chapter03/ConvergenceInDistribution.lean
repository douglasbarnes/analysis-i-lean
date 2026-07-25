/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.VCPermanence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Chapter 3: Measurable convergence in distribution

Direct Chapter 3 wrappers around Mathlib's proved convergence-in-distribution,
continuous-mapping, and Slutsky theorems.  These are the measurable special
cases of the outer-law principles used in Section 3.7.
-/

noncomputable section

open scoped Topology
open Filter ProbabilityTheory

namespace InfiniteDimensionalStatistics
namespace Chapter03

section ContinuousMapping

variable {ι E F Ω' : Type*} {Ω : ι → Type*}
  {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} [TopologicalSpace E] [OpensMeasurableSpace E]
  {mF : MeasurableSpace F} [TopologicalSpace F] [BorelSpace F]
  {X : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι}

/-- Measurable continuous-mapping theorem. -/
theorem tendstoInDistribution_continuous_comp
    {g : E → F} (hg : Continuous g)
    (h : MeasureTheory.TendstoInDistribution X l Z μ μ') :
    MeasureTheory.TendstoInDistribution
      (fun i ↦ g ∘ X i) l (g ∘ Z) μ μ' :=
  h.continuous_comp hg

end ContinuousMapping

section ProbabilityImpliesDistribution

variable {E Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  [SeminormedAddCommGroup E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

/-- Convergence in probability implies convergence in distribution. -/
theorem tendstoInDistribution_of_tendstoInMeasure
    {X : ℕ → Ω → E} {Z : Ω → E}
    (hX : ∀ n, AEMeasurable (X n) μ)
    (hZ : AEMeasurable Z μ)
    (h : TendstoInMeasure μ X atTop Z) :
    MeasureTheory.TendstoInDistribution X atTop Z (fun _ ↦ μ) μ :=
  h.tendstoInDistribution hX hZ

end ProbabilityImpliesDistribution

section Slutsky

variable {E Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  [SeminormedAddCommGroup E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

/-- Slutsky theorem for addition of a term converging in probability to zero. -/
theorem tendstoInDistribution_add_negligible
    {X Y : ℕ → Ω → E} {Z : Ω → E}
    (hXZ : MeasureTheory.TendstoInDistribution X atTop Z (fun _ ↦ μ) μ)
    (hYX : TendstoInMeasure μ (Y - X) atTop 0)
    (hY : ∀ n, AEMeasurable (Y n) μ) :
    MeasureTheory.TendstoInDistribution Y atTop Z (fun _ ↦ μ) μ :=
  MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub Y Z hXZ hYX hY

end Slutsky

end Chapter03
end InfiniteDimensionalStatistics
