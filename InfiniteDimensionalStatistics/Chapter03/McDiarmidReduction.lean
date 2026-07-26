/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.AzumaHoeffding

/-!
# Chapter 3: McDiarmid reduction to Doob increments

The two-sided bounded-differences concentration theorem is reduced to an
explicit conditionally sub-Gaussian Doob decomposition.  The remaining theorem
obligation is to construct this certificate from `HasBoundedDifferences` for an
independent product sample.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Reduction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ}

/--
A certificate that a statistic's centred value is represented by a finite sum
of conditionally sub-Gaussian adapted increments.
-/
structure DoobSubgaussianCertificate
    (Z : Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (cY : ℕ → ℝ≥0) (n : ℕ) : Prop where
  adapted : StronglyAdapted ℱ Y
  initial : HasSubgaussianMGF (Y 0) (cY 0) μ
  conditional : ∀ i < n - 1,
    HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
      (Y (i + 1)) (cY (i + 1)) μ
  sum_eq_centered : ∀ ω,
    ∑ i ∈ Finset.range n, Y i ω = Z ω - μ[Z]

/-- Upper-tail concentration from a Doob sub-Gaussian certificate. -/
theorem mcdiarmid_upper_of_doob_certificate
    (Z : Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (cY : ℕ → ℝ≥0) (n : ℕ)
    (hcert : DoobSubgaussianCertificate (μ := μ) (ℱ := ℱ) Z Y cY n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ Z ω - μ[Z]} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  have h := azumaHoeffding_upper
    hcert.adapted hcert.initial n hcert.conditional hε
  convert h using 1
  ext ω
  rw [hcert.sum_eq_centered]

/-- Lower-tail concentration from a Doob sub-Gaussian certificate. -/
theorem mcdiarmid_lower_of_doob_certificate
    (Z : Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (cY : ℕ → ℝ≥0) (n : ℕ)
    (hcert : DoobSubgaussianCertificate (μ := μ) (ℱ := ℱ) Z Y cY n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ -(Z ω - μ[Z])} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  have h := azumaHoeffding_lower
    hcert.adapted hcert.initial n hcert.conditional hε
  convert h using 1
  ext ω
  rw [hcert.sum_eq_centered]

/-- Two-sided concentration from a Doob sub-Gaussian certificate. -/
theorem mcdiarmid_two_sided_of_doob_certificate
    (Z : Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (cY : ℕ → ℝ≥0) (n : ℕ)
    (hcert : DoobSubgaussianCertificate (μ := μ) (ℱ := ℱ) Z Y cY n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |Z ω - μ[Z]|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  have h := azumaHoeffding_two_sided
    hcert.adapted hcert.initial n hcert.conditional hε
  convert h using 1
  ext ω
  rw [hcert.sum_eq_centered]

end Reduction

end Chapter03
end InfiniteDimensionalStatistics
