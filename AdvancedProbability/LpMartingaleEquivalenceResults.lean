import AdvancedProbability.LpMartingaleConvergenceResults

noncomputable section

open scoped ENNReal NNReal Topology MeasureTheory ProbabilityTheory
open Filter MeasureTheory

namespace AdvancedProbability

universe u

/-- A discrete process is bounded in the finite real `Lᵖ` space. -/
def BoundedInLpOfReal {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (p : ℝ) : Prop :=
  ∃ R : ℝ≥0, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ R

/-- A discrete process converges almost surely and in the finite real `Lᵖ` space. -/
def ConvergesInLpOfReal {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (p : ℝ) : Prop :=
  ∃ Z : Ω → ℝ, MemLp Z (ENNReal.ofReal p) μ ∧
    (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Z ω))) ∧
    Tendsto (fun n ↦ eLpNorm (X n - Z) (ENNReal.ofReal p) μ) atTop (𝓝 0)

/-- A martingale has an `Lᵖ` terminal representation. -/
def HasTerminalRepresentationLpOfReal {Ω : Type u} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (p : ℝ) : Prop :=
  ∃ Z : Ω → ℝ, MemLp Z (ENNReal.ofReal p) μ ∧
    ∀ n, X n =ᵐ[μ] μ[Z | ℱ n]

/-- Source 41: the `Lᵖ` martingale convergence theorem for every finite real `p > 1`.

The following are equivalent: boundedness in `Lᵖ`, almost-sure and `Lᵖ` convergence, and an
`Lᵖ` terminal conditional-expectation representation.  In the terminal representation, the limit
is the conditional expectation of the terminal variable with respect to `⨆ n, ℱ n`. -/
theorem DiscreteLpMartingaleConvergenceTheorem
    {Ω : Type u} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m₀} {X : ℕ → Ω → ℝ}
    (hX : Martingale X ℱ μ) {p : ℝ} (hp : 1 < p) :
    (BoundedInLpOfReal μ X p ↔ ConvergesInLpOfReal μ X p) ∧
    (ConvergesInLpOfReal μ X p ↔ HasTerminalRepresentationLpOfReal μ ℱ X p) ∧
    (∀ Z : Ω → ℝ, MemLp Z (ENNReal.ofReal p) μ →
      (∀ n, X n =ᵐ[μ] μ[Z | ℱ n]) →
        (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop
          (𝓝 (μ[Z | ⨆ n, ℱ n] ω))) ∧
        Tendsto (fun n ↦ eLpNorm (X n - μ[Z | ⨆ n, ℱ n])
          (ENNReal.ofReal p) μ) atTop (𝓝 0)) := by
  have hp1 : 1 ≤ p := hp.le
  have hleInf : (⨆ n, ℱ n) ≤ m₀ := iSup_le fun n ↦ ℱ.le n
  have hterminalData : ∀ Z : Ω → ℝ, MemLp Z (ENNReal.ofReal p) μ →
      (∀ n, X n =ᵐ[μ] μ[Z | ℱ n]) →
        (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop
          (𝓝 (μ[Z | ⨆ n, ℱ n] ω))) ∧
        Tendsto (fun n ↦ eLpNorm (X n - μ[Z | ⨆ n, ℱ n])
          (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
    intro Z hZ hrep
    constructor
    · have hrepAll : ∀ᵐ ω ∂μ, ∀ n, X n ω = μ[Z | ℱ n] ω := by
        rw [ae_all_iff]
        exact hrep
      filter_upwards [hrepAll, MeasureTheory.tendsto_ae_condExp (ℱ := ℱ) Z] with ω hω ht
      have hfun : (fun n ↦ X n ω) = fun n ↦ μ[Z | ℱ n] ω := funext hω
      rw [hfun]
      exact ht
    · have ht := MemLp.tendsto_eLpNorm_condExp_ofReal hp1 hZ (ℱ := ℱ)
      refine ht.congr' (Eventually.of_forall fun n ↦ ?_)
      exact (eLpNorm_congr_ae ((hrep n).sub EventuallyEq.rfl)).symm
  have hboundedToConvergent :
      BoundedInLpOfReal μ X p → ConvergesInLpOfReal μ X p := by
    rintro ⟨R, hR⟩
    have hconv := hX.ae_tendsto_and_eLpNorm_tendsto_ofReal hp hR
    exact ⟨ℱ.limitProcess X μ, hX.submartingale.memLp_limitProcess hR, hconv.1, hconv.2⟩
  have hconvergentToTerminal :
      ConvergesInLpOfReal μ X p → HasTerminalRepresentationLpOfReal μ ℱ X p := by
    rintro ⟨Z, hZ, -, hLp⟩
    exact ⟨Z, hZ, fun n ↦ hX.eq_condExp_of_tendsto_eLpNorm_ofReal hp1 hZ hLp n⟩
  have hterminalToBounded :
      HasTerminalRepresentationLpOfReal μ ℱ X p → BoundedInLpOfReal μ X p := by
    rintro ⟨Z, hZ, hrep⟩
    refine ⟨(eLpNorm Z (ENNReal.ofReal p) μ).toNNReal, fun n ↦ ?_⟩
    calc
      eLpNorm (X n) (ENNReal.ofReal p) μ =
          eLpNorm μ[Z | ℱ n] (ENNReal.ofReal p) μ := eLpNorm_congr_ae (hrep n)
      _ ≤ eLpNorm Z (ENNReal.ofReal p) μ :=
        eLpNorm_condExp_le_eLpNorm_ofReal (ℱ.le n) hp1 Z
      _ = ↑(eLpNorm Z (ENNReal.ofReal p) μ).toNNReal :=
        (ENNReal.coe_toNNReal hZ.eLpNorm_ne_top).symm
  have hterminalToConvergent :
      HasTerminalRepresentationLpOfReal μ ℱ X p → ConvergesInLpOfReal μ X p := by
    rintro ⟨Z, hZ, hrep⟩
    have hdata := hterminalData Z hZ hrep
    exact ⟨μ[Z | ⨆ n, ℱ n], memLp_condExp_ofReal hleInf hp1 hZ, hdata.1, hdata.2⟩
  exact
    ⟨⟨hboundedToConvergent, fun hconv ↦ hterminalToBounded (hconvergentToTerminal hconv)⟩,
      ⟨hconvergentToTerminal, hterminalToConvergent⟩,
      hterminalData⟩

end AdvancedProbability
