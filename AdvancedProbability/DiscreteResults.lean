import AdvancedProbability.DiscreteMartingales

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory ProbabilityTheory Function
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u

/-- Source 39: Doob's maximal inequality for a non-negative discrete submartingale. -/
theorem DiscreteMaximalInequalityTheorem {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ m₀}
    {X : ℕ → Ω → ℝ} (hX : Submartingale X ℱ μ) (hX_nonnegative : 0 ≤ X)
    {ε : ℝ≥0} (N : ℕ) :
    ε * μ {ω | (ε : ℝ) ≤
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun k ↦ X k ω)} ≤
      ENNReal.ofReal
        (∫ ω in {ω | (ε : ℝ) ≤
          (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun k ↦ X k ω)},
          X N ω ∂μ) :=
  MeasureTheory.maximal_ineq hX hX_nonnegative N

/-- A martingale has a terminal representation when all its values are conditional expectations of
one integrable terminal random variable. -/
def HasTerminalRepresentation {Ω : Type u} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) : Prop :=
  ∃ Z : Ω → ℝ, Integrable Z μ ∧ ∀ n, X n =ᵐ[μ] μ[Z | ℱ n]

/-- Convergence in `L¹`, expressed using Mathlib's `eLpNorm`. -/
def ConvergesInL1 {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∃ Z : Ω → ℝ, Integrable Z μ ∧
    Tendsto (fun n ↦ eLpNorm (X n - Z) 1 μ) atTop (𝓝 0)

/-- Source 42: the three standard equivalent forms of the `L¹` martingale convergence theorem.

A martingale is uniformly integrable iff it has an integrable terminal representation, and this is
also equivalent to convergence in `L¹` to an integrable limit. -/
theorem DiscreteL1MartingaleConvergenceTheorem {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ m₀}
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ) :
    (UniformIntegrable X 1 μ ↔ HasTerminalRepresentation μ ℱ X) ∧
      (HasTerminalRepresentation μ ℱ X ↔ ConvergesInL1 μ X) := by
  constructor
  · constructor
    · intro hUI
      obtain ⟨R, hR⟩ := hUI.2.2
      refine ⟨ℱ.limitProcess X μ, ?_, fun n ↦ hX.ae_eq_condExp_limitProcess hUI n⟩
      exact (hX.submartingale.memLp_limitProcess hR).integrable le_rfl
    · rintro ⟨Z, hZ, hrep⟩
      exact hZ.uniformIntegrable_condExp_filtration.ae_eq fun n ↦ (hrep n).symm
  · constructor
    · rintro ⟨Z, hZ, hrep⟩
      let Zlim : Ω → ℝ := μ[Z | ⨆ n, ℱ n]
      refine ⟨Zlim, ?_, ?_⟩
      · exact integrable_condExp
      · have ht := MeasureTheory.tendsto_eLpNorm_condExp (ℱ := ℱ) Z
        refine ht.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
        exact eLpNorm_congr_ae ((hrep n).sub (EventuallyEq.rfl))
    · rintro ⟨Z, hZ, ht⟩
      exact ⟨Z, hZ, fun n ↦ hX.eq_condExp_of_tendsto_eLpNorm hZ ht n⟩

end AdvancedProbability
