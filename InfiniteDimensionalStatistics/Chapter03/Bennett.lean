/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.Rademacher
import Mathlib.Probability.Moments.Basic

/-!
# Chapter 3: Bennett and Bernstein interfaces

This file separates Bennett's bounded-variable mgf estimate from its Chernoff
consequences.  The generic Chernoff step is proved.  Establishing the mgf
predicate from the hypotheses of Theorem 3.1.5 remains the substantive local
analysis theorem.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

/--
Bennett's one-sided mgf estimate with variance proxy `v` and scale `c`.
The degenerate case `c = 0` is intentionally excluded from uses by a separate
positivity hypothesis.
-/
def HasBennettMGF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (v c : ℝ) : Prop :=
  (∀ λ : ℝ, 0 ≤ λ → Integrable (fun ω ↦ Real.exp (λ * X ω)) μ) ∧
  ∀ λ : ℝ, 0 ≤ λ →
    mgf X μ λ ≤
      Real.exp ((v / c ^ 2) * (Real.exp (λ * c) - λ * c - 1))

namespace HasBennettMGF

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} {X : Ω → ℝ} {v c : ℝ}

/-- Exponential Markov bound obtained from a Bennett mgf estimate. -/
theorem measure_ge_le_exp
    (h : HasBennettMGF μ X v c)
    {t λ : ℝ} (hλ : 0 ≤ λ) :
    μ.real {ω | t ≤ X ω} ≤
      Real.exp
        (-λ * t + (v / c ^ 2) *
          (Real.exp (λ * c) - λ * c - 1)) := by
  calc
    μ.real {ω | t ≤ X ω}
        ≤ Real.exp (-λ * t) * mgf X μ λ :=
      measure_ge_le_exp_mul_mgf t hλ (h.1 λ hλ)
    _ ≤ Real.exp (-λ * t) *
        Real.exp ((v / c ^ 2) *
          (Real.exp (λ * c) - λ * c - 1)) := by
      gcongr
      · positivity
      · exact h.2 λ hλ
    _ = Real.exp
        (-λ * t + (v / c ^ 2) *
          (Real.exp (λ * c) - λ * c - 1)) := by
      rw [Real.exp_add]

/-- The Bennett optimizing parameter for `v,c,t > 0`. -/
def optimalParameter (v c t : ℝ) : ℝ :=
  Real.log (1 + c * t / v) / c

/-- The exponent in the optimized Bennett bound. -/
def optimizedExponent (v c t : ℝ) : ℝ :=
  -(v / c ^ 2) * bennettFunction (c * t / v)

/--
Chernoff bound evaluated at Bennett's optimizing parameter.  The algebraic
identification with `optimizedExponent` is stated separately so that source
constant conventions remain visible.
-/
theorem measure_ge_le_at_optimal
    (h : HasBennettMGF μ X v c)
    (hv : 0 < v) (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤
      Real.exp
        (-optimalParameter v c t * t + (v / c ^ 2) *
          (Real.exp (optimalParameter v c t * c) -
            optimalParameter v c t * c - 1)) := by
  apply h.measure_ge_le_exp
  unfold optimalParameter
  positivity

end HasBennettMGF

/-- The quadratic-linear Bernstein exponent used in Proposition 3.1.6. -/
def bernsteinTailBound (v c t : ℝ) : ℝ :=
  Real.exp (-bernsteinExponent v c t)

end Chapter03
end InfiniteDimensionalStatistics
