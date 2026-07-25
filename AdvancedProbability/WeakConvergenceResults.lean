import AdvancedProbability.WeakConvergence

noncomputable section

open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace
open Set Filter MeasureTheory

namespace AdvancedProbability

/-- Source 87: Lévy's continuity theorem. -/
theorem LevyContinuityTheorem (μ : ℕ → ProbabilityMeasure ℝ) {f : ℝ → ℂ}
    (hf : ContinuousAt f 0)
    (h : ∀ t : ℝ,
      Tendsto (fun n ↦ characteristicFunction (μ n : Measure ℝ) t) atTop (𝓝 (f t))) :
    ∃ μ₀ : ProbabilityMeasure ℝ,
      (∀ t : ℝ, characteristicFunction (μ₀ : Measure ℝ) t = f t) ∧
        Tendsto μ atTop (𝓝 μ₀) := by
  have h_tight : IsTightMeasureSet (Set.range fun n ↦ (μ n : Measure ℝ)) :=
    isTightMeasureSet_of_tendsto_charFun hf (by
      intro t
      simpa [characteristicFunction] using h t)
  have h_compact : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using h_tight)
  obtain ⟨μ₀, -, φ, hφ_mono, hφ⟩ :=
    h_compact.tendsto_subseq (fun n ↦ subset_closure (Set.mem_range_self n))
  have h_char : ∀ t : ℝ, characteristicFunction (μ₀ : Measure ℝ) t = f t := by
    intro t
    have h₁ : Tendsto (fun n ↦ characteristicFunction (μ (φ n) : Measure ℝ) t)
        atTop (𝓝 (characteristicFunction (μ₀ : Measure ℝ) t)) := by
      have hcf :=
        (ProbabilityMeasure.tendsto_iff_tendsto_charFun
          (μ := fun n ↦ μ (φ n)) (μ₀ := μ₀)).1 hφ t
      simpa [characteristicFunction] using hcf
    have h₂ : Tendsto (fun n ↦ characteristicFunction (μ (φ n) : Measure ℝ) t)
        atTop (𝓝 (f t)) := by
      simpa [Function.comp_def] using (h t).comp hφ_mono.tendsto_atTop
    exact tendsto_nhds_unique h₁ h₂
  refine ⟨μ₀, h_char, ?_⟩
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have ht := h t
  rw [← h_char t] at ht
  simpa [characteristicFunction] using ht

end AdvancedProbability
