/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.MourierStrongLaw
import Mathlib.Probability.CentralLimitTheorem

/-!
# Chapter 3: Scalar central limit theorem

Chapter 3 wrappers around Mathlib's scalar central limit theorem.  These give
the one-dimensional and Cramér–Wold projection inputs used by empirical-process
weak convergence criteria.  A separate multivariate measure-convergence theorem
is still needed to assemble all finite projections into vector convergence.
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

section EmpiricalCoordinateCLT

variable {Ω Ω' S : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
variable {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/--
Central limit theorem for one fixed empirical-process coordinate `f`.

For an i.i.d. sample `Xᵢ`, the centred normalized sums of `f(Xᵢ)` converge to a
Gaussian with variance `Var[f(X₀)]`.
-/
theorem empirical_process_coordinate_clt
    (X : ℕ → Ω → S) (f : S → ℝ) (hf : Measurable f)
    (Y : Ω' → ℝ)
    (hY : HasLaw Y
      (gaussianReal 0 Var[f ∘ X 0; P].toNNReal) P')
    (hf2 : MemLp (f ∘ X 0) 2 P)
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, f (X k ω) - n * P[f ∘ X 0]))
      atTop Y (fun _ => P) P' := by
  apply scalar_central_limit (fun i => f ∘ X i) Y hY hf2
  · exact hindep.comp (fun _ => f) (fun _ => hf)
  · intro i
    exact (hident i).comp hf

/--
Cramér–Wold projection CLT for a finite family of empirical-process
coordinates.  Every deterministic linear combination of the centred coordinate
sums converges to the matching scalar Gaussian law.
-/
theorem empirical_process_linear_combination_clt
    {m : ℕ} (X : ℕ → Ω → S)
    (f : Fin m → S → ℝ) (hf : ∀ i, Measurable (f i))
    (a : Fin m → ℝ) (Y : Ω' → ℝ)
    (hY : HasLaw Y
      (gaussianReal 0
        Var[(fun x => ∑ i, a i * f i x) ∘ X 0; P].toNNReal) P')
    (hf2 : ∀ i, MemLp (f i ∘ X 0) 2 P)
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
        ((∑ k ∈ Finset.range n, ∑ i, a i * f i (X k ω)) -
          n * P[(fun x => ∑ i, a i * f i x) ∘ X 0]))
      atTop Y (fun _ => P) P' := by
  let g : S → ℝ := fun x => ∑ i, a i * f i x
  have hg : Measurable g := by
    exact Finset.measurable_fun_sum _ fun i _ => (hf i).const_mul (a i)
  have hg2 : MemLp (g ∘ X 0) 2 P := by
    change MemLp (fun ω => ∑ i, a i * f i (X 0 ω)) 2 P
    exact memLp_finsetSum' _ fun i _ => (hf2 i).const_mul (a i)
  simpa [g] using
    empirical_process_coordinate_clt X g hg Y hY hg2 hindep hident

end EmpiricalCoordinateCLT

end Chapter03
end InfiniteDimensionalStatistics
