/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.RademacherMoments
import InfiniteDimensionalStatistics.Chapter03.SubgaussianMaximum

/-!
# Chapter 3: Optimized finite sub-Gaussian maximum

Optimization of the positive Chernoff parameter in Theorem 3.1.10.  The
strictly positive proxy and `2 ≤ |ι|` hypotheses isolate the nondegenerate case;
the zero-proxy and singleton cases can be handled separately from the
sub-Gaussian zero-law API.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section OptimizedMaximum

variable {Ω ι : Type*} [MeasurableSpace Ω]
  [Fintype ι] [Nonempty ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Z : ι → Ω → ℝ} {M : Ω → ℝ}

/--
A finite family with common positive sub-Gaussian proxy `σ²` satisfies

`E maxᵢ Zᵢ ≤ √(2 σ² log |ι|)`

when the index type has at least two elements.
-/
theorem integral_max_le_subgaussian_sqrt
    (σ2 : ℝ≥0) (hσ2 : 0 < (σ2 : ℝ))
    (hcard : 1 < Fintype.card ι)
    (hmax : IsPointwiseFiniteMaximum Z M)
    (hM : Integrable M μ)
    (hExpM : ∀ λ : ℝ, Integrable (fun ω => Real.exp (λ * M ω)) μ)
    (hZ : ∀ i, HasSubgaussianMGF (Z i) σ2 μ) :
    (∫ ω, M ω ∂μ) ≤
      Real.sqrt (2 * (σ2 : ℝ) * Real.log (Fintype.card ι : ℝ)) := by
  let s : ℝ := (σ2 : ℝ)
  let L : ℝ := Real.log (Fintype.card ι : ℝ)
  have hcard_real : 1 < (Fintype.card ι : ℝ) := by
    exact_mod_cast hcard
  have hL : 0 < L := by
    exact Real.log_pos hcard_real
  have hs : 0 < s := hσ2
  let λ : ℝ := Real.sqrt (2 * L / s)
  have hλarg : 0 < 2 * L / s := by positivity
  have hλ : 0 < λ := by
    exact Real.sqrt_pos.2 hλarg
  have hλsq : λ ^ 2 = 2 * L / s := by
    exact Real.sq_sqrt hλarg.le
  have hλsq' : s * λ ^ 2 = 2 * L := by
    rw [hλsq]
    field_simp [hs.ne']
  have hLrepr : L = s * λ ^ 2 / 2 := by
    nlinarith [hλsq']
  have hsqrt :
      Real.sqrt (2 * s * L) = s * λ := by
    apply (Real.sqrt_eq_iff_eq_sq
      (by positivity : 0 ≤ 2 * s * L)
      (mul_nonneg hs.le (Real.sqrt_nonneg _))).2
    calc
      2 * s * L = s * (2 * L) := by ring
      _ = s * (s * λ ^ 2) := by rw [hλsq']
      _ = (s * λ) ^ 2 := by ring
  have hbound := integral_max_le_subgaussian_parameter
    σ2 hλ hmax hM (hExpM λ) hZ
  calc
    (∫ ω, M ω ∂μ) ≤
        λ⁻¹ * (L + s * λ ^ 2 / 2) := by
      simpa [s, L] using hbound
    _ = s * λ := by
      rw [hLrepr]
      field_simp [hλ.ne']
      ring
    _ = Real.sqrt (2 * s * L) := hsqrt.symm
    _ = Real.sqrt (2 * (σ2 : ℝ) *
        Real.log (Fintype.card ι : ℝ)) := by rfl

end OptimizedMaximum

end Chapter03
end InfiniteDimensionalStatistics
