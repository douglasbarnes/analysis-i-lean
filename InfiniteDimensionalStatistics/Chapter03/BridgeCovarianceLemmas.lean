/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.EmpiricalAlgebra
import Mathlib.Probability.Moments.Variance

/-!
# Chapter 3: Brownian-bridge covariance lemmas

Identification of the chapter's covariance kernel with Mathlib covariance and
variance under the source's probability and `L²` hypotheses, including finite
bilinearity and the variance formula for Cramér–Wold projections.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Covariance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The local covariance definition is Mathlib covariance with reordered arguments. -/
theorem covariance_eq_mathlib (P : Measure Ω) (X Y : Ω → ℝ) :
    covariance P X Y = ProbabilityTheory.covariance X Y P :=
  rfl

/-- Local covariance is symmetric. -/
theorem covariance_comm (P : Measure Ω) (X Y : Ω → ℝ) :
    covariance P X Y = covariance P Y X := by
  simpa [covariance_eq_mathlib] using
    (ProbabilityTheory.covariance_comm (μ := P) X Y)

end Covariance

section BrownianBridge

variable {S : Type*} [MeasurableSpace S]
  {P : Measure S} [IsProbabilityMeasure P]

/-- The bridge kernel is Mathlib covariance. -/
theorem brownianBridgeCovariance_eq_covariance
    {f g : S → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    brownianBridgeCovariance P f g =
      ProbabilityTheory.covariance f g P := by
  symm
  exact ProbabilityTheory.covariance_eq_sub hf hg

/-- The bridge covariance is symmetric. -/
theorem brownianBridgeCovariance_comm
    {f g : S → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    brownianBridgeCovariance P f g =
      brownianBridgeCovariance P g f := by
  rw [brownianBridgeCovariance_eq_covariance hf hg,
    brownianBridgeCovariance_eq_covariance hg hf]
  exact ProbabilityTheory.covariance_comm f g

/-- Diagonal bridge covariance is Mathlib variance. -/
theorem brownianBridgeCovariance_self_eq_variance
    {f : S → ℝ} (hf : MemLp f 2 P) :
    brownianBridgeCovariance P f f =
      ProbabilityTheory.variance f P := by
  rw [brownianBridgeCovariance_eq_covariance hf hf]
  exact ProbabilityTheory.covariance_self hf.aemeasurable

/-- Diagonal bridge covariance is nonnegative. -/
theorem brownianBridgeCovariance_self_nonneg
    {f : S → ℝ} (hf : MemLp f 2 P) :
    0 ≤ brownianBridgeCovariance P f f := by
  rw [brownianBridgeCovariance_self_eq_variance hf]
  exact ProbabilityTheory.variance_nonneg f P

/-- The intrinsic bridge metric is nonnegative. -/
theorem brownianBridgeMetric_nonneg (f g : S → ℝ) :
    0 ≤ brownianBridgeMetric P f g :=
  Real.sqrt_nonneg _

/-- The bridge metric is symmetric under `L²(P)` hypotheses. -/
theorem brownianBridgeMetric_comm
    {f g : S → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    brownianBridgeMetric P f g = brownianBridgeMetric P g f := by
  unfold brownianBridgeMetric
  have hfg : MemLp (fun x ↦ f x - g x) 2 P := hf.sub hg
  have hgf : MemLp (fun x ↦ g x - f x) 2 P := hg.sub hf
  rw [brownianBridgeCovariance_self_eq_variance hfg,
    brownianBridgeCovariance_self_eq_variance hgf]
  have hneg : (fun x ↦ g x - f x) = fun x ↦ -(f x - g x) := by
    funext x
    ring
  rw [hneg]
  simpa using ProbabilityTheory.variance_const_mul (-1)
    (fun x ↦ f x - g x) P

/--
Bilinearity of the bridge covariance for finite linear combinations.
-/
theorem brownianBridgeCovariance_linear_combinations
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (f : ι → S → ℝ)
    (b : κ → ℝ) (g : κ → S → ℝ)
    (hf : ∀ i, MemLp (f i) 2 P)
    (hg : ∀ j, MemLp (g j) 2 P) :
    brownianBridgeCovariance P
        (fun x => ∑ i, a i * f i x)
        (fun x => ∑ j, b j * g j x) =
      ∑ i, ∑ j, a i * b j * brownianBridgeCovariance P (f i) (g j) := by
  have hfa : ∀ i, MemLp (fun x => a i * f i x) 2 P :=
    fun i => (hf i).const_mul (a i)
  have hgb : ∀ j, MemLp (fun x => b j * g j x) 2 P :=
    fun j => (hg j).const_mul (b j)
  have hsumf : MemLp (fun x => ∑ i, a i * f i x) 2 P :=
    memLp_finsetSum' _ fun i _ => hfa i
  have hsumg : MemLp (fun x => ∑ j, b j * g j x) 2 P :=
    memLp_finsetSum' _ fun j _ => hgb j
  rw [brownianBridgeCovariance_eq_covariance hsumf hsumg]
  rw [ProbabilityTheory.covariance_fun_sum_fun_sum hfa hgb]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right,
    ← brownianBridgeCovariance_eq_covariance (hf i) (hg j)]
  ring

/--
Variance of a finite linear combination in terms of the bridge covariance
matrix.
-/
theorem variance_linear_combination_eq_bridge_covariance
    {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (f : ι → S → ℝ)
    (hf : ∀ i, MemLp (f i) 2 P) :
    Var[(fun x => ∑ i, a i * f i x); P] =
      ∑ i, ∑ j, a i * a j * brownianBridgeCovariance P (f i) (f j) := by
  have hsum : MemLp (fun x => ∑ i, a i * f i x) 2 P :=
    memLp_finsetSum' _ fun i _ => (hf i).const_mul (a i)
  rw [← brownianBridgeCovariance_self_eq_variance hsum]
  exact brownianBridgeCovariance_linear_combinations a f a f hf hf

end BrownianBridge

end Chapter03
end InfiniteDimensionalStatistics
