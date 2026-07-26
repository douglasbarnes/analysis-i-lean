/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.ScalarCentralLimit
import Mathlib.Probability.Moments.SubGaussian

/-!
# Chapter 3: Azuma–Hoeffding martingale tails

Chapter 3 wrappers around Mathlib's conditionally sub-Gaussian martingale-sum
theorem.  This isolates the remaining McDiarmid obligation: deriving the
conditional sub-Gaussian bounds for the Doob increments from the chapter's
bounded-differences predicate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section ConditionalNegation

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ}
  [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : Ω → ℝ} {c : ℝ≥0}

/-- Conditional sub-Gaussianity is invariant under negation. -/
theorem hasCondSubgaussianMGF_neg
    (hX : HasCondSubgaussianMGF m hm X c μ) :
    HasCondSubgaussianMGF m hm (fun ω => -X ω) c μ := by
  unfold HasCondSubgaussianMGF at hX ⊢
  simpa only [Pi.neg_apply] using hX.neg

end ConditionalNegation

section Azuma

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0}
  {ℱ : Filtration ℕ mΩ}

/-- Upper-tail Azuma–Hoeffding inequality. -/
theorem azumaHoeffding_upper
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ)
    (n : ℕ)
    (h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
        (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  exact ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
    h_adapted h0 n h_subG hε

/-- Lower-tail Azuma–Hoeffding inequality. -/
theorem azumaHoeffding_lower
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ)
    (n : ℕ)
    (h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
        (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ -(∑ i ∈ Finset.range n, Y i ω)} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  have hneg := azumaHoeffding_upper
    (Y := fun i ω => -Y i ω) (cY := cY)
    h_adapted.neg h0.neg n
    (fun i hi => hasCondSubgaussianMGF_neg (h_subG i hi)) hε
  simpa [Finset.sum_neg_distrib] using hneg

/-- Two-sided Azuma–Hoeffding inequality. -/
theorem azumaHoeffding_two_sided
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ)
    (n : ℕ)
    (h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
        (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  let A : Set Ω := {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}
  let B : Set Ω := {ω | ε ≤ -(∑ i ∈ Finset.range n, Y i ω)}
  have hsubset :
      {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|} ⊆ A ∪ B := by
    intro ω hω
    rcases (le_abs.mp hω) with hpos | hneg
    · exact Or.inl hpos
    · exact Or.inr hneg
  have hu := azumaHoeffding_upper h_adapted h0 n h_subG hε
  have hl := azumaHoeffding_lower h_adapted h0 n h_subG hε
  calc
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|} ≤
        μ.real (A ∪ B) :=
      measureReal_mono hsubset (measure_union_ne_top (by finiteness) (by finiteness))
    _ ≤ μ.real A + μ.real B := measureReal_union_le A B
    _ ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) +
        Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) :=
      add_le_add hu hl
    _ = 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by ring

end Azuma

end Chapter03
end InfiniteDimensionalStatistics
