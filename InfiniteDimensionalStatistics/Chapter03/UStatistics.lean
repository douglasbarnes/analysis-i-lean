/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.EmpiricalEntropy

/-!
# Chapter 3: Canonical U-statistics

The order-two U-statistic and degeneracy interfaces from Section 3.4.  The
source-sensitive definitions of the four scales `A`, `B`, `C`, and `D` are kept
as an explicit record pending direct transcription of pp. 176–177.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section OrderTwo

variable {S Ω : Type*} [MeasurableSpace S]

/-- Ordered pairs `i<j` used by an order-two U-statistic. -/
def pairIndex (n : ℕ) :=
  {p : Fin n × Fin n // p.1 < p.2}

instance (n : ℕ) : Fintype (pairIndex n) := Fintype.ofFinite (pairIndex n)

/--
An order-two U-statistic with potentially index-dependent kernels.

Source: unnumbered definitions on pp. 176–177; specification id
`canonical_Ustat`.
-/
def orderTwoUStatistic {n : ℕ}
    (X : Fin n → Ω → S)
    (h : Fin n → Fin n → S → S → ℝ) : Ω → ℝ :=
  fun ω ↦ ∑ p : pairIndex n,
    h p.1.1 p.1.2 (X p.1.1 ω) (X p.1.2 ω)

/-- Degeneracy in the first coordinate of a kernel. -/
def IsCanonicalInFirstCoordinate
    (P : Measure S) (h : S → S → ℝ) : Prop :=
  ∀ y, (∫ x, h x y ∂P) = 0

/-- Degeneracy in the second coordinate of a kernel. -/
def IsCanonicalInSecondCoordinate
    (P : Measure S) (h : S → S → ℝ) : Prop :=
  ∀ x, (∫ y, h x y ∂P) = 0

/-- A kernel is canonical when both one-coordinate integrals vanish. -/
def IsCanonicalKernel (P : Measure S) (h : S → S → ℝ) : Prop :=
  IsCanonicalInFirstCoordinate P h ∧
    IsCanonicalInSecondCoordinate P h

/-- Every kernel in an indexed order-two statistic is canonical. -/
def IsCanonicalKernelFamily {n : ℕ}
    (P : Measure S) (h : Fin n → Fin n → S → S → ℝ) : Prop :=
  ∀ i j, i < j → IsCanonicalKernel P (h i j)

/--
The four nonnegative scales used in the order-two U-statistic inequality.
Their exact formulas are deliberately not guessed: `Chapter03.yaml` marks the
source display as requiring direct page-image transcription.
-/
structure UStatisticScales where
  A : ℝ≥0
  B : ℝ≥0
  C : ℝ≥0
  D : ℝ≥0

/-- The four-term deviation profile from Theorem 3.4.8. -/
def UStatisticScales.deviationProfile
    (s : UStatisticScales) (u : ℝ) : ℝ :=
  s.C * Real.sqrt u + s.D * u + s.B * u ^ (3 / 2 : ℝ) + s.A * u ^ 2

/-- Pointwise uniform kernel bound associated with scale `A`. -/
def HasUniformKernelScale {n : ℕ}
    (h : Fin n → Fin n → S → S → ℝ) (A : ℝ≥0) : Prop :=
  ∀ i j x y, i < j → |h i j x y| ≤ A

/-- Global square-integrability scale associated with `C`. -/
def HasGlobalL2KernelScale {n : ℕ}
    (P : Measure S) (h : Fin n → Fin n → S → S → ℝ) (C : ℝ≥0) : Prop :=
  ∑ p : pairIndex n,
      ∫ x, ∫ y, h p.1.1 p.1.2 x y ^ 2 ∂P ∂P ≤ C ^ 2

end OrderTwo

end Chapter03
end InfiniteDimensionalStatistics
