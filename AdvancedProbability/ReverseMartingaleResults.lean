import AdvancedProbability.DiscreteMartingales
import Exchangeability.Probability.Martingale.Convergence

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory ProbabilityTheory Function
open Set Filter MeasureTheory ProbabilityTheory

namespace AdvancedProbability

universe u

/-- Source 45: Lévy's downward theorem.  Along an antitone sequence of sub-sigma-algebras,
conditional expectations of an integrable random variable converge both almost surely and in
`L¹` to the conditional expectation on the intersection sigma-algebra. -/
theorem BackwardMartingaleConvergenceTheorem {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (𝒢 : ℕ → MeasurableSpace Ω) (hanti : Antitone 𝒢)
    (hle : ∀ n, 𝒢 n ≤ m₀) (f : Ω → ℝ) (hf : Integrable f μ) :
    (∀ᵐ ω ∂μ, Tendsto (fun n ↦ μ[f | 𝒢 n] ω) atTop
      (𝓝 (μ[f | ⨅ n, 𝒢 n] ω))) ∧
    Tendsto (fun n ↦ eLpNorm (μ[f | 𝒢 n] - μ[f | ⨅ n, 𝒢 n]) 1 μ)
      atTop (𝓝 0) := by
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ μ[f | 𝒢 n] ω) atTop
      (𝓝 (μ[f | ⨅ n, 𝒢 n] ω)) :=
    Exchangeability.Probability.condExp_tendsto_iInf hanti hle f hf
  refine ⟨hae, ?_⟩
  apply tendsto_Lp_finite_of_tendsto_ae (hp := le_refl 1) (hp' := ENNReal.one_ne_top)
  · intro n
    exact (integrable_condExp : Integrable (μ[f | 𝒢 n]) μ).aestronglyMeasurable
  · exact memLp_one_iff_integrable.2
      (integrable_condExp : Integrable (μ[f | ⨅ n, 𝒢 n]) μ)
  · exact (hf.uniformIntegrable_condExp hle).unifIntegrable
  · exact hae

end AdvancedProbability
