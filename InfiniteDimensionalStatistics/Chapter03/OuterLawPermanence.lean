/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.OuterMeasureLemmas

/-!
# Chapter 3: Outer-law permanence

Continuous images preserve bounded-continuous tests, outer convergence in law,
asymptotic measurability and compact containment.  Finite-dimensional outer
convergence is also inherited after reindexing a process.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section ContinuousTests

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- Composition with a continuous map preserves bounded continuous tests. -/
theorem IsBoundedContinuousTest.comp
    {h : F → ℝ} (hh : IsBoundedContinuousTest h)
    {f : E → F} (hf : Continuous f) :
    IsBoundedContinuousTest (h ∘ f) := by
  refine ⟨hh.1.comp hf, ?_⟩
  rcases hh.2 with ⟨M, hM, hbound⟩
  exact ⟨M, hM, fun x => hbound (f x)⟩

end ContinuousTests

section ContinuousImages

variable {Ω E F : Type*} [MeasurableSpace Ω]
  [TopologicalSpace E] [MeasurableSpace E]
  [TopologicalSpace F] [MeasurableSpace F]

/-- Continuous mapping theorem for convergence in outer law. -/
theorem ConvergesInOuterLaw.continuous_comp
    (P : ℕ → Measure Ω) (X : ℕ → Ω → E)
    (Q : Measure Ω) (Y : Ω → E)
    (hX : ConvergesInOuterLaw P X Q Y)
    {f : E → F} (hf : Continuous f) :
    ConvergesInOuterLaw P
      (fun n ω => f (X n ω)) Q (fun ω => f (Y ω)) := by
  intro h hh
  simpa [Function.comp_def] using hX (h ∘ f) (hh.comp hf)

/-- Asymptotic measurability is preserved by continuous maps. -/
theorem IsAsymptoticallyMeasurable.continuous_comp
    (P : ℕ → Measure Ω) (X : ℕ → Ω → E)
    (hX : IsAsymptoticallyMeasurable P X)
    {f : E → F} (hf : Continuous f) :
    IsAsymptoticallyMeasurable P (fun n ω => f (X n ω)) := by
  intro h hh
  simpa [Function.comp_def] using hX (h ∘ f) (hh.comp hf)

/-- Strong outer compact containment is preserved by continuous maps. -/
theorem IsOuterAsymptoticallyTight.continuous_comp
    (P : ℕ → Measure Ω) (X : ℕ → Ω → E)
    (hX : IsOuterAsymptoticallyTight P X)
    {f : E → F} (hf : Continuous f) :
    IsOuterAsymptoticallyTight P (fun n ω => f (X n ω)) := by
  intro ε hε
  rcases hX ε hε with ⟨K, hK, N, hN⟩
  refine ⟨f '' K, hK.image hf, N, fun n hn => ?_⟩
  calc
    outerProbability (P n)
        (outsideCompactEvent (fun ω => f (X n ω)) (f '' K)) ≤
      outerProbability (P n) (outsideCompactEvent (X n) K) := by
        apply outerProbability_mono
        intro ω hω
        intro hmem
        exact hω ⟨X n ω, hmem, rfl⟩
    _ ≤ ENNReal.ofReal ε := hN n hn

end ContinuousImages

section FiniteDimensionalRestriction

variable {Ω T U : Type*} [MeasurableSpace Ω]

/-- Finite-dimensional outer convergence is inherited by every reindexed subprocess. -/
theorem FiniteDimensionalOuterConvergence.comp
    (P : ℕ → Measure Ω) (X : ℕ → Ω → T → ℝ)
    (Q : Measure Ω) (Y : Ω → T → ℝ)
    (hX : FiniteDimensionalOuterConvergence P X Q Y)
    (ι : U → T) :
    FiniteDimensionalOuterConvergence P
      (fun n ω u => X n ω (ι u)) Q
      (fun ω u => Y ω (ι u)) := by
  intro m t
  simpa [finiteEvaluation, Function.comp_def] using
    hX m (fun i => ι (t i))

end FiniteDimensionalRestriction

end Chapter03
end InfiniteDimensionalStatistics
