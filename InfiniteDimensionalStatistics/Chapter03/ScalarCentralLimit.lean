/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.MourierStrongLaw
import Mathlib.Probability.CentralLimitTheorem

/-!
# Chapter 3: Scalar central limit theorem

A Chapter 3 wrapper around Mathlib's scalar central limit theorem.  This is the
one-dimensional finite-distribution input used by the empirical-process weak
convergence criteria.  A separate Cramér–Wold/multivariate layer is still needed
for arbitrary finite index families.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Real Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section ScalarCLT

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/--
Scalar central limit theorem for i.i.d. `L²` random variables.

The normalized centred sums converge in distribution to a real Gaussian with
variance `Var[X₀]`; the zero-variance case is included.
-/
theorem scalar_central_limit
    (X : ℕ → Ω → ℝ) (Y : Ω' → ℝ)
    (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P)
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ => P) P' := by
  exact ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
    hY hX hindep hident

/-- Standardized scalar central limit theorem. -/
theorem scalar_central_limit_standard
    (X : ℕ → Ω → ℝ) (Y : Ω' → ℝ)
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hmean : P[X 0] = 0)
    (hsecond : P[X 0 ^ 2] = 1)
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
        ∑ k ∈ Finset.range n, X k ω)
      atTop Y (fun _ => P) P' := by
  exact ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum
    hY hmean hsecond hindep hident

end ScalarCLT

end Chapter03
end InfiniteDimensionalStatistics
