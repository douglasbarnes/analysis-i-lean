import AdvancedProbability.LpConditionalUniformResults
import Mathlib.Probability.Martingale.Convergence

noncomputable section

open scoped ENNReal NNReal Topology MeasureTheory ProbabilityTheory
open Filter MeasureTheory

namespace AdvancedProbability

universe u

/-- Lévy's upward theorem in every finite real `Lᵖ`, `p ≥ 1`. -/
theorem MemLp.tendsto_eLpNorm_condExp_ofReal
    {Ω : Type u} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m₀} {p : ℝ} (hp : 1 ≤ p)
    {f : Ω → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ) :
    Tendsto
      (fun n ↦ eLpNorm (μ[f | ℱ n] - μ[f | ⨆ n, ℱ n]) (ENNReal.ofReal p) μ)
      atTop (𝓝 0) := by
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hqone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hle : (⨆ n, ℱ n) ≤ m₀ := iSup_le fun n ↦ ℱ.le n
  exact tendsto_Lp_finite_of_tendsto_ae hqone hqtop
    (fun n ↦ (stronglyMeasurable_condExp.mono (ℱ.le n)).aestronglyMeasurable)
    (memLp_condExp_ofReal hle hp hf)
    (MemLp.uniformIntegrable_condExp_ofReal hp hf (fun n ↦ ℱ.le n)).unifIntegrable
    (MeasureTheory.tendsto_ae_condExp (ℱ := ℱ) f)

end AdvancedProbability
