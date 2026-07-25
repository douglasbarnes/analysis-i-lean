import AdvancedProbability.LpConditionalResults
import AdvancedProbability.DiscreteResults

noncomputable section

open scoped ENNReal NNReal Topology MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u

/-- If a martingale converges in a finite real `Lᵖ`, then every term is the conditional expectation
of the limiting random variable.  This is the finite-`p` analogue of Mathlib's
`Martingale.eq_condExp_of_tendsto_eLpNorm`. -/
theorem Martingale.eq_condExp_of_tendsto_eLpNorm_ofReal
    {Ω : Type u} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m₀} {X : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hX : Martingale X ℱ μ) {p : ℝ} (hp : 1 ≤ p)
    (hg : MemLp g (ENNReal.ofReal p) μ)
    (hgtends : Tendsto (fun n ↦ eLpNorm (X n - g) (ENNReal.ofReal p) μ) atTop (𝓝 0))
    (n : ℕ) : X n =ᵐ[μ] μ[g | ℱ n] := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.2 hp_pos)
  have h1p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hg_int : Integrable g μ :=
    memLp_one_iff_integrable.1 (hg.mono_exponent h1p)
  rw [← sub_ae_eq_zero,
    ← eLpNorm_eq_zero_iff
      (((hX.stronglyMeasurable n).mono (ℱ.le n)).sub
        (stronglyMeasurable_condExp.mono (ℱ.le n))).aestronglyMeasurable hp0]
  have ht : Tendsto (fun m ↦ eLpNorm (μ[X m - g | ℱ n]) (ENNReal.ofReal p) μ)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgtends
      (fun _ ↦ zero_le) fun m ↦
        eLpNorm_condExp_le_eLpNorm_ofReal (ℱ.le n) hp (X m - g)
  have hev : ∀ m ≥ n,
      eLpNorm (μ[X m - g | ℱ n]) (ENNReal.ofReal p) μ =
        eLpNorm (X n - μ[g | ℱ n]) (ENNReal.ofReal p) μ := by
    intro m hm
    refine eLpNorm_congr_ae ((condExp_sub (hX.integrable m) hg_int _).trans ?_)
    filter_upwards [hX.2 n m hm] with x hx
    simp only [hx, Pi.sub_apply]
  exact tendsto_nhds_unique (tendsto_atTop_of_eventually_const hev) ht

end AdvancedProbability
