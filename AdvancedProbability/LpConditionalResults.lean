import AdvancedProbability.DoobLpImported
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

noncomputable section

open scoped ENNReal NNReal Topology MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u

/-- Conditional Jensen for the convex function `x ↦ ‖x‖ ^ p`, specialized to real-valued
conditional expectations and finite real exponents. -/
theorem condExp_norm_rpow_le {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {p : ℝ} (hp : 1 ≤ p)
    {f : Ω → ℝ} (hfint : Integrable (fun x ↦ ‖f x‖ ^ p) μ) :
    (fun x ↦ ‖μ[f | m] x‖ ^ p) ≤ᵐ[μ] μ[(fun x ↦ ‖f x‖ ^ p) | m] := by
  have hp' : 0 < p := by linarith
  by_cases hf_int : Integrable f μ
  · have hl :=
      (Real.continuous_rpow_const hp'.le).lowerSemicontinuous.lowerSemicontinuousOn (Set.Ici 0)
    have hj := (convexOn_rpow hp).map_condExp_le hm hl (by simp) isClosed_Ici hf_int.norm hfint
    filter_upwards [norm_condExp_le f, hj] with a ha hb
    exact (Real.rpow_le_rpow (norm_nonneg _) ha hp'.le).trans hb
  · simp only [condExp_of_not_integrable hf_int, Pi.zero_apply, norm_zero,
      Real.zero_rpow hp'.ne.symm]
    apply condExp_nonneg
    filter_upwards with a
    positivity

/-- Conditional expectation contracts the integral of the `p`-th power of the norm. -/
theorem integral_norm_condExp_rpow_le {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {p : ℝ} (hp : 1 ≤ p)
    {f : Ω → ℝ} (hf : Integrable (fun x ↦ ‖f x‖ ^ p) μ) :
    ∫ x, ‖μ[f | m] x‖ ^ p ∂μ ≤ ∫ x, ‖f x‖ ^ p ∂μ := calc
  _ ≤ ∫ x, μ[(fun x ↦ ‖f x‖ ^ p) | m] x ∂μ := by
    refine integral_mono_of_nonneg ?_ integrable_condExp (condExp_norm_rpow_le hm hp hf)
    filter_upwards with a
    positivity
  _ = _ := integral_condExp hm

/-- A finite-exponent `Lᵖ` random variable remains in `Lᵖ` after conditional expectation. -/
theorem memLp_condExp_ofReal {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {p : ℝ} (hp : 1 ≤ p)
    {f : Ω → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (μ[f | m]) (ENNReal.ofReal p) μ := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.2 hp_pos)
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← integrable_norm_rpow_iff integrable_condExp.1 hp0 hpt]
  rw [ENNReal.toReal_ofReal hp_pos.le]
  have hf_pow : Integrable (fun x ↦ ‖f x‖ ^ p) μ := by
    rw [← ENNReal.toReal_ofReal hp_pos.le]
    exact (integrable_norm_rpow_iff hf.1 hp0 hpt).2 hf
  refine Integrable.mono_nonneg integrable_condExp ?_ ?_ (condExp_norm_rpow_le hm hp hf_pow)
  · fun_prop
  · filter_upwards with a
    positivity

/-- Conditional expectation is a contraction in every finite real `Lᵖ`, `p ≥ 1`. -/
theorem eLpNorm_condExp_le_eLpNorm_ofReal {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {p : ℝ} (hp : 1 ≤ p)
    (f : Ω → ℝ) :
    eLpNorm (μ[f | m]) (ENNReal.ofReal p) μ ≤ eLpNorm f (ENNReal.ofReal p) μ := by
  by_cases hf : MemLp f (ENNReal.ofReal p) μ
  · have hce := memLp_condExp_ofReal hm hp hf
    rw [← ofReal_lpNorm hf, ← ofReal_lpNorm hce]
    apply ENNReal.ofReal_le_ofReal
    have hp_pos : 0 < p := zero_lt_one.trans_le hp
    have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.2 hp_pos)
    have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hpt hf.1,
      lpNorm_eq_integral_norm_rpow_toReal hp0 hpt hce.1,
      ENNReal.toReal_ofReal hp_pos.le]
    gcongr
    exact integral_norm_condExp_rpow_le hm hp <| by
      rw [← ENNReal.toReal_ofReal hp_pos.le]
      exact (integrable_norm_rpow_iff hf.1 hp0 hpt).2 hf
  · simp only [MemLp, not_and, not_lt, top_le_iff] at hf
    by_cases ha : AEStronglyMeasurable f μ
    · simp [hf ha]
    · simp [condExp_of_not_integrable (fun h ↦ ha h.aestronglyMeasurable)]

end AdvancedProbability
