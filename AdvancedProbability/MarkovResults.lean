import AdvancedProbability.DiscreteResults

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory ProbabilityTheory Function
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u v

/-- Source 52: a bounded harmonic function evaluated along a Markov chain is a martingale.

The one-step Markov property is stated as the conditional-expectation identity for the next state.
Harmonicity turns its right-hand side into the present value. Boundedness supplies integrability on
the finite measure space, and Mathlib's adjacent-time martingale criteria then give the result for
all pairs of times. -/
theorem BoundedHarmonicMartingaleTheorem {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ m₀}
    {E : Type v} [Fintype E] (P : E → E → ℝ) (f : E → ℝ)
    (X : ℕ → Ω → E) (hharmonic : HarmonicFor E P f)
    (hadapted : StronglyAdapted ℱ (fun n ω ↦ f (X n ω)))
    (hbounded : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hmarkov : ∀ n,
      μ[fun ω ↦ f (X (n + 1) ω) | ℱ n] =ᵐ[μ]
        fun ω ↦ ∑ y, P (X n ω) y * f y) :
    Martingale (fun n ω ↦ f (X n ω)) ℱ μ := by
  obtain ⟨C, hC⟩ := hbounded
  have hintegrable : ∀ n, Integrable (fun ω ↦ f (X n ω)) μ := by
    intro n
    refine Integrable.of_bound ((hadapted n).mono (ℱ.le n)).aestronglyMeasurable C ?_
    exact ae_of_all μ fun ω ↦ by
      simpa [Real.norm_eq_abs] using hC (X n ω)
  have hstep : ∀ n,
      μ[fun ω ↦ f (X (n + 1) ω) | ℱ n] =ᵐ[μ] fun ω ↦ f (X n ω) := by
    intro n
    exact (hmarkov n).trans <| ae_of_all μ fun ω ↦ by
      simpa using hharmonic (X n ω)
  exact martingale_iff.mpr
    ⟨supermartingale_nat hadapted hintegrable fun n ↦ (hstep n).le,
      submartingale_nat hadapted hintegrable fun n ↦ (hstep n).symm.le⟩

end AdvancedProbability
