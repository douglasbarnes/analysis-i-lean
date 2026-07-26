/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.SubgaussianMaximumOptimized

/-!
# Chapter 3: Bennett optimizer algebra

Exact reduction of the Chernoff exponent at Bennett's optimizing parameter to
`-(v/c²) h(ct/v)`.  This completes the optimization step of Proposition 3.1.6
conditional on the bounded-variable Bennett mgf estimate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

namespace HasBennettMGF

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {X : Ω → ℝ} {v c t : ℝ}

/-- The optimizing parameter times the scale is the logarithmic Bennett coordinate. -/
theorem optimalParameter_mul_scale
    (hc : c ≠ 0) :
    optimalParameter v c t * c = Real.log (1 + c * t / v) := by
  unfold optimalParameter
  field_simp

/-- The exponential at the optimizing parameter recovers `1 + ct/v`. -/
theorem exp_optimalParameter_mul_scale
    (hv : 0 < v) (hc : 0 < c) (ht : 0 ≤ t) :
    Real.exp (optimalParameter v c t * c) = 1 + c * t / v := by
  rw [optimalParameter_mul_scale hc.ne', Real.exp_log]
  have hu : 0 ≤ c * t / v := by positivity
  linarith

/-- The optimized Chernoff exponent is exactly the Bennett exponent. -/
theorem chernoffExponent_optimal_eq
    (hv : 0 < v) (hc : 0 < c) (ht : 0 ≤ t) :
    -optimalParameter v c t * t + (v / c ^ 2) *
        (Real.exp (optimalParameter v c t * c) -
          optimalParameter v c t * c - 1) =
      optimizedExponent v c t := by
  rw [exp_optimalParameter_mul_scale hv hc ht,
    optimalParameter_mul_scale hc.ne']
  unfold optimizedExponent bennettFunction
  field_simp [hv.ne', hc.ne']
  ring

/-- Optimized Bennett tail bound, conditional on `HasBennettMGF`. -/
theorem measure_ge_le_bennett
    (h : HasBennettMGF μ X v c)
    (hv : 0 < v) (hc : 0 < c) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤
      Real.exp (optimizedExponent v c t) := by
  have hopt := h.measure_ge_le_at_optimal hv hc ht
  rw [chernoffExponent_optimal_eq hv hc ht] at hopt
  exact hopt

/-- Expanded form of the optimized Bennett tail bound. -/
theorem measure_ge_le_bennett_expanded
    (h : HasBennettMGF μ X v c)
    (hv : 0 < v) (hc : 0 < c) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤
      Real.exp (-(v / c ^ 2) * bennettFunction (c * t / v)) := by
  simpa [optimizedExponent] using h.measure_ge_le_bennett hv hc ht

end HasBennettMGF

end Chapter03
end InfiniteDimensionalStatistics
