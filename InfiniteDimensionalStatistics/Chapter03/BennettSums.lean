/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.BennettMGF
import InfiniteDimensionalStatistics.Chapter03.BennettOptimization

/-!
# Chapter 3: Bennett inequalities for independent sums

Bennett mgf certificates are stable under independent addition.  This file
assembles Theorem 3.1.5 into the exact Bennett tail bound for finite sums of
independent centred uniformly bounded random variables.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

namespace HasBennettMGF

section Addition

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X Y : Ω → ℝ} {vX vY c : ℝ}

/-- Independent Bennett variables with a common scale have additive variance proxies. -/
theorem add_of_indepFun
    (hX : HasBennettMGF μ X vX c)
    (hY : HasBennettMGF μ Y vY c)
    (hindep : X ⟂ᵢ[μ] Y) :
    HasBennettMGF μ (fun ω => X ω + Y ω) (vX + vY) c := by
  constructor
  · intro λ hλ
    exact hindep.integrable_exp_mul_add (hX.1 λ hλ) (hY.1 λ hλ)
  · intro λ hλ
    let A : ℝ := Real.exp (λ * c) - λ * c - 1
    calc
      mgf (fun ω => X ω + Y ω) μ λ
          = mgf X μ λ * mgf Y μ λ := by
              simpa only [Pi.add_apply] using
                hindep.mgf_add (hX.1 λ hλ).aestronglyMeasurable
                  (hY.1 λ hλ).aestronglyMeasurable
      _ ≤ Real.exp ((vX / c ^ 2) * A) *
          Real.exp ((vY / c ^ 2) * A) := by
            gcongr
            · exact mgf_nonneg
            · exact hX.2 λ hλ
            · exact hY.2 λ hλ
      _ = Real.exp (((vX + vY) / c ^ 2) * A) := by
            rw [← Real.exp_add]
            congr 1
            ring

end Addition

section FiniteSums

variable {Ω ι : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ι → Ω → ℝ} {v : ι → ℝ} {c : ℝ}

/-- A finite independent sum of Bennett variables has the sum of their variance proxies. -/
theorem finsetSum_of_iIndepFun
    (hindep : iIndepFun X μ)
    (hX : ∀ i, Measurable (X i))
    {s : Finset ι}
    (hB : ∀ i ∈ s, HasBennettMGF μ (X i) (v i) c) :
    HasBennettMGF μ (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, v i) c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.notMem_empty, Finset.sum_empty]
      constructor
      · intro λ _
        simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => 1) μ)
      · intro λ _
        simp [mgf]
  | insert i s hi ih =>
      have hiB : HasBennettMGF μ (X i) (v i) c := hB i (Finset.mem_insert_self i s)
      have hsB : ∀ j ∈ s, HasBennettMGF μ (X j) (v j) c :=
        fun j hj => hB j (Finset.mem_insert_of_mem hj)
      have hsumB := ih hsB
      have hi_indep_sum : X i ⟂ᵢ[μ] (fun ω => ∑ j ∈ s, X j ω) := by
        simpa only [Finset.sum_apply] using
          (hindep.indepFun_finsetSum_of_notMem hX hi).symm
      simpa [Finset.sum_insert hi] using hiB.add_of_indepFun hsumB hi_indep_sum

end FiniteSums

end HasBennettMGF

section BoundedIndependentSums

variable {Ω ι : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ι → Ω → ℝ} {c : ℝ}

/--
Bennett mgf estimate for a finite independent sum of centred variables bounded
in absolute value by the common scale `c`.
-/
theorem bounded_independent_sum_hasBennettMGF
    (hc : 0 < c)
    (hindep : iIndepFun X μ)
    (hX : ∀ i, Measurable (X i))
    {s : Finset ι}
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ c)
    (hmean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = 0) :
    HasBennettMGF μ (fun ω => ∑ i ∈ s, X i ω)
      (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) c := by
  apply HasBennettMGF.finsetSum_of_iIndepFun hindep hX
  intro i hi
  exact hasBennettMGF_of_ae_abs_le (hX i).aemeasurable hc
    (hbound i hi) (hmean i hi) rfl

/-- Exact Bennett upper tail for a finite independent bounded centred sum. -/
theorem bounded_independent_sum_bennett_tail
    (hc : 0 < c)
    (hindep : iIndepFun X μ)
    (hX : ∀ i, Measurable (X i))
    {s : Finset ι}
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ c)
    (hmean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = 0)
    {t : ℝ} (ht : 0 ≤ t)
    (hv : 0 < ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) :
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
      Real.exp
        (-((∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) / c ^ 2) *
          bennettFunction
            (c * t / (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ))) := by
  have hB := bounded_independent_sum_hasBennettMGF hc hindep hX hbound hmean
  simpa only [Finset.sum_apply] using
    hB.measure_ge_le_bennett_expanded hv hc ht

end BoundedIndependentSums

end Chapter03
end InfiniteDimensionalStatistics
