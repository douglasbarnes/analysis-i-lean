/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.BennettSums
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Chapter 3: Bennett-to-Bernstein relaxation

The scalar calculus in Proposition 3.1.6 is proved here.  The principal estimate is

`h₁(u) ≥ u² / (2(1+u/3))`, `u ≥ 0`,

where `h₁(u)=(1+u)log(1+u)-u`.  Combining it with the optimized Bennett
bound yields the usual quadratic-linear Bernstein exponent.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Real Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section LogarithmicLowerBound

/-- The derivative used in the elementary logarithmic lower bound. -/
theorem hasDerivAt_log_one_add_sub_two_mul_div
    {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt
      (fun x : ℝ => Real.log (1 + x) - 2 * x / (2 + x))
      (u ^ 2 / ((1 + u) * (2 + u) ^ 2)) u := by
  have h1 : (1 + u : ℝ) ≠ 0 := by positivity
  have h2 : (2 + u : ℝ) ≠ 0 := by positivity
  have harg1 : HasDerivAt (fun x : ℝ => 1 + x) 1 u := by
    simpa using (hasDerivAt_const u 1).add (hasDerivAt_id u)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + u)) u := by
    convert harg1.log h1 using 1 <;> field_simp
  have hnum : HasDerivAt (fun x : ℝ => 2 * x) 2 u := by
    simpa using (hasDerivAt_id u).const_mul 2
  have hden : HasDerivAt (fun x : ℝ => 2 + x) 1 u := by
    simpa using (hasDerivAt_const u 2).add (hasDerivAt_id u)
  have hquot : HasDerivAt (fun x : ℝ => 2 * x / (2 + x))
      (4 / (2 + u) ^ 2) u := by
    convert hnum.div hden h2 using 1
    field_simp [h2]
    ring
  convert hlog.sub hquot using 1
  field_simp [h1, h2]
  ring

/-- For `u ≥ 0`, `log(1+u) ≥ 2u/(2+u)`. -/
theorem two_mul_div_le_log_one_add {u : ℝ} (hu : 0 ≤ u) :
    2 * u / (2 + u) ≤ Real.log (1 + u) := by
  let f : ℝ → ℝ := fun x => Real.log (1 + x) - 2 * x / (2 + x)
  have hf_cont : ContinuousOn f (Set.Ici 0) := by
    intro x hx
    exact (hasDerivAt_log_one_add_sub_two_mul_div hx).continuousAt.continuousWithinAt
  have hf_diff : DifferentiableOn ℝ f (interior (Set.Ici 0)) := by
    intro x hx
    exact (hasDerivAt_log_one_add_sub_two_mul_div (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hf_deriv : ∀ x ∈ interior (Set.Ici 0), 0 ≤ deriv f x := by
    intro x hx
    rw [(hasDerivAt_log_one_add_sub_two_mul_div (interior_subset hx)).deriv]
    positivity
  have hmono := (convex_Ici : Convex ℝ (Set.Ici (0 : ℝ))).mul_sub_le_image_sub_of_le_deriv
    hf_cont hf_diff hf_deriv 0 (by simp) u hu hu
  simpa [f] using hmono

end LogarithmicLowerBound

section BennettFunctionCalculus

/-- The derivative of Bennett's function is `log(1+u)` on the nonnegative axis. -/
theorem hasDerivAt_bennettFunction
    {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt bennettFunction (Real.log (1 + u)) u := by
  have h1 : (1 + u : ℝ) ≠ 0 := by positivity
  have harg : HasDerivAt (fun x : ℝ => 1 + x) 1 u := by
    simpa using (hasDerivAt_const u 1).add (hasDerivAt_id u)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + u)) u := by
    convert harg.log h1 using 1 <;> field_simp
  have hprod := harg.mul hlog
  have hsub := hprod.sub (hasDerivAt_id u)
  convert hsub using 1
  · ext x
    simp [bennettFunction]
  · field_simp [h1]
    ring

/-- Derivative of the rational Bernstein comparison term. -/
theorem hasDerivAt_three_mul_sq_div
    {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt
      (fun x : ℝ => 3 * x ^ 2 / (2 * (x + 3)))
      (3 * u * (u + 6) / (2 * (u + 3) ^ 2)) u := by
  have h3 : (u + 3 : ℝ) ≠ 0 := by positivity
  have hnum : HasDerivAt (fun x : ℝ => 3 * x ^ 2) (6 * u) u := by
    convert (hasDerivAt_pow 2 u).const_mul 3 using 1 <;> ring
  have hden : HasDerivAt (fun x : ℝ => 2 * (x + 3)) 2 u := by
    convert ((hasDerivAt_id u).const_add 3).const_mul 2 using 1 <;> ring
  convert hnum.div hden (by positivity : 2 * (u + 3) ≠ 0) using 1
  field_simp [h3]
  ring

/-- Derivative of the gap between Bennett and Bernstein functions. -/
theorem hasDerivAt_bennett_gap
    {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt
      (fun x : ℝ => bennettFunction x - 3 * x ^ 2 / (2 * (x + 3)))
      (Real.log (1 + u) - 3 * u * (u + 6) / (2 * (u + 3) ^ 2)) u := by
  exact (hasDerivAt_bennettFunction hu).sub (hasDerivAt_three_mul_sq_div hu)

/-- Rational comparison used after the logarithmic lower bound. -/
theorem three_mul_div_le_two_mul_div {u : ℝ} (hu : 0 ≤ u) :
    3 * u * (u + 6) / (2 * (u + 3) ^ 2) ≤ 2 * u / (2 + u) := by
  have hleft : 0 < 2 * (u + 3) ^ 2 := by positivity
  have hright : 0 < 2 + u := by positivity
  apply (div_le_div_iff₀ hleft hright).2
  nlinarith [mul_nonneg hu (sq_nonneg u)]

/--
The Bennett function dominates the quadratic-linear Bernstein comparison.
-/
theorem three_mul_sq_div_le_bennettFunction {u : ℝ} (hu : 0 ≤ u) :
    3 * u ^ 2 / (2 * (u + 3)) ≤ bennettFunction u := by
  let f : ℝ → ℝ := fun x => bennettFunction x - 3 * x ^ 2 / (2 * (x + 3))
  have hf_cont : ContinuousOn f (Set.Ici 0) := by
    intro x hx
    exact (hasDerivAt_bennett_gap hx).continuousAt.continuousWithinAt
  have hf_diff : DifferentiableOn ℝ f (interior (Set.Ici 0)) := by
    intro x hx
    exact (hasDerivAt_bennett_gap (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hf_deriv : ∀ x ∈ interior (Set.Ici 0), 0 ≤ deriv f x := by
    intro x hx
    have hx0 : 0 ≤ x := interior_subset hx
    rw [(hasDerivAt_bennett_gap hx0).deriv]
    have hlog := two_mul_div_le_log_one_add hx0
    have hrat := three_mul_div_le_two_mul_div hx0
    linarith
  have hmono := (convex_Ici : Convex ℝ (Set.Ici (0 : ℝ))).mul_sub_le_image_sub_of_le_deriv
    hf_cont hf_diff hf_deriv 0 (by simp) u hu hu
  simpa [f, bennettFunction] using hmono

/-- Standard form `h₁(u) ≥ u²/(2(1+u/3))`. -/
theorem bernstein_ratio_le_bennettFunction {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 / (2 * (1 + u / 3)) ≤ bennettFunction u := by
  convert three_mul_sq_div_le_bennettFunction hu using 1
  field_simp
  ring

end BennettFunctionCalculus

section TailRelaxation

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} {X : Ω → ℝ} {v c t : ℝ}

/-- Bernstein quadratic-linear tail bound from a Bennett mgf certificate. -/
theorem HasBennettMGF.measure_ge_le_bernstein
    (h : HasBennettMGF μ X v c)
    (hv : 0 < v) (hc : 0 < c) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤
      Real.exp (-bernsteinExponent v c t) := by
  have hB := h.measure_ge_le_bennett_expanded hv hc ht
  have hu : 0 ≤ c * t / v := by positivity
  have hlower := bernstein_ratio_le_bennettFunction hu
  refine hB.trans ?_
  rw [Real.exp_le_exp]
  have hscale : 0 ≤ v / c ^ 2 := by positivity
  calc
    -(v / c ^ 2) * bennettFunction (c * t / v)
        ≤ -(v / c ^ 2) *
          ((c * t / v) ^ 2 / (2 * (1 + (c * t / v) / 3))) := by
            exact mul_le_mul_of_nonpos_left hlower (neg_nonpos.mpr hscale)
    _ = -bernsteinExponent v c t := by
          unfold bernsteinExponent
          field_simp [hv.ne', hc.ne']
          ring

/-- Bernstein upper tail for a finite independent bounded centred sum. -/
theorem bounded_independent_sum_bernstein_tail
    {ι : Type*} [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ}
    (hc : 0 < c)
    (hindep : iIndepFun Y μ)
    (hY : ∀ i, Measurable (Y i))
    {s : Finset ι}
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |Y i ω| ≤ c)
    (hmean : ∀ i ∈ s, (∫ ω, Y i ω ∂μ) = 0)
    (hv : 0 < ∑ i ∈ s, ∫ ω, Y i ω ^ 2 ∂μ)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, Y i ω} ≤
      Real.exp
        (-bernsteinExponent
          (∑ i ∈ s, ∫ ω, Y i ω ^ 2 ∂μ) c t) := by
  have hB := bounded_independent_sum_hasBennettMGF hc hindep hY hbound hmean
  simpa only [Finset.sum_apply] using hB.measure_ge_le_bernstein hv hc ht

end TailRelaxation

end Chapter03
end InfiniteDimensionalStatistics
