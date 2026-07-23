import AdvancedProbability.LpConditionalResults
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

noncomputable section

open scoped ENNReal NNReal Topology MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u v

/-- A family with one common almost-everywhere norm bound is uniformly integrable in every finite
nonzero `Lᵖ`. -/
theorem unifIntegrable_of_ae_bound {Ω : Type u} [MeasurableSpace Ω] {ι : Type v}
    {μ : Measure Ω} {F : ι → Ω → ℝ} {q : ℝ≥0∞}
    (hq0 : q ≠ 0) (hqtop : q ≠ ∞) {M : ℝ} (hM : 0 < M)
    (hF : ∀ i, ∀ᵐ x ∂μ, ‖F i x‖ ≤ M) :
    UnifIntegrable F q μ := by
  intro ε hε
  refine ⟨(ε / M) ^ q.toReal, Real.rpow_pos_of_pos (div_pos hε hM) _, fun i s hs hμs ↦ ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have haebdd : ∀ᵐ x ∂μ.restrict s, ‖F i x‖ ≤ M := ae_restrict_of_ae (hF i)
  refine (eLpNorm_le_of_ae_bound haebdd).trans ?_
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    ← ENNReal.le_div_iff_mul_le (Or.inl _) (Or.inl ENNReal.ofReal_ne_top)]
  · rw [ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hq0 hqtop)]
    refine hμs.trans ?_
    rw [← ENNReal.ofReal_rpow_of_pos (div_pos hε hM)]
    gcongr
    rw [ENNReal.ofReal_div_of_pos hM]
  · simpa only [ENNReal.ofReal_eq_zero, not_le, Ne]

/-- Conditional expectations of a fixed finite real `Lᵖ` random variable form a uniformly
integrable `Lᵖ` family. -/
theorem MemLp.uniformIntegrable_condExp_ofReal
    {Ω : Type u} [m₀ : MeasurableSpace Ω] {ι : Type v}
    {μ : Measure Ω} [IsFiniteMeasure μ] {p : ℝ} (hp : 1 ≤ p)
    {f : Ω → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ)
    {𝒢 : ι → MeasurableSpace Ω} (h𝒢 : ∀ i, 𝒢 i ≤ m₀) :
    UniformIntegrable (fun i ↦ μ[f | 𝒢 i]) (ENNReal.ofReal p) μ := by
  letI : MeasurableSpace Ω := m₀
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  have hq0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.2 hp_pos)
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hqone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hf_int : Integrable f μ :=
    memLp_one_iff_integrable.1 (hf.mono_exponent hqone)
  refine ⟨fun i ↦ (stronglyMeasurable_condExp.mono (h𝒢 i)).aestronglyMeasurable, ?_, ?_⟩
  · intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    have hη0 : ENNReal.ofReal (ε / 2) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.2 hε2)
    obtain ⟨g, hfg, hg⟩ := hf.exists_simpleFunc_eLpNorm_sub_lt hqtop hη0
    have hg_int : Integrable (fun x ↦ g x) μ :=
      memLp_one_iff_integrable.1 (hg.mono_exponent hqone)
    obtain ⟨C, hC⟩ := g.exists_forall_norm_le
    let M : ℝ := max C 0 + 1
    have hM : 0 < M := by dsimp [M]; linarith [le_max_right C 0]
    let R : ℝ≥0 := ⟨M, hM.le⟩
    have hg_bound : ∀ x, |g x| ≤ (R : ℝ) := by
      intro x
      change ‖g x‖ ≤ M
      exact (hC x).trans (by dsimp [M]; linarith [le_max_left C 0])
    have hCEg_bound : ∀ i, ∀ᵐ x ∂μ, ‖μ[(fun x ↦ g x) | 𝒢 i] x‖ ≤ M := by
      intro i
      simpa [Real.norm_eq_abs, R] using
        (ae_bdd_condExp_of_ae_bdd (μ := μ) (m := 𝒢 i) (R := R)
          (f := fun x ↦ g x) (ae_of_all μ hg_bound))
    have hUIg : UnifIntegrable (fun i ↦ μ[(fun x ↦ g x) | 𝒢 i])
        (ENNReal.ofReal p) μ :=
      unifIntegrable_of_ae_bound hq0 hqtop hM hCEg_bound
    obtain ⟨δ, hδ, hUIgδ⟩ := hUIg hε2
    refine ⟨δ, hδ, fun i s hs hμs ↦ ?_⟩
    have hsplit : μ[f | 𝒢 i] =ᵐ[μ]
        μ[f - (fun x ↦ g x) | 𝒢 i] + μ[(fun x ↦ g x) | 𝒢 i] := by
      simpa only [sub_add_cancel] using
        (condExp_add (hf_int.sub hg_int) hg_int (𝒢 i))
    have hind : s.indicator μ[f | 𝒢 i] =ᵐ[μ]
        s.indicator μ[f - (fun x ↦ g x) | 𝒢 i] +
          s.indicator μ[(fun x ↦ g x) | 𝒢 i] := by
      filter_upwards [hsplit] with x hx
      by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs, hx]
    calc
      eLpNorm (s.indicator μ[f | 𝒢 i]) (ENNReal.ofReal p) μ
          = eLpNorm
              (s.indicator μ[f - (fun x ↦ g x) | 𝒢 i] +
                s.indicator μ[(fun x ↦ g x) | 𝒢 i]) (ENNReal.ofReal p) μ :=
            eLpNorm_congr_ae hind
      _ ≤ eLpNorm (s.indicator μ[f - (fun x ↦ g x) | 𝒢 i]) (ENNReal.ofReal p) μ +
            eLpNorm (s.indicator μ[(fun x ↦ g x) | 𝒢 i]) (ENNReal.ofReal p) μ := by
            apply eLpNorm_add_le
            · exact (stronglyMeasurable_condExp.mono (h𝒢 i)).aestronglyMeasurable.indicator hs
            · exact (stronglyMeasurable_condExp.mono (h𝒢 i)).aestronglyMeasurable.indicator hs
            · exact hqone
      _ ≤ eLpNorm (f - (fun x ↦ g x)) (ENNReal.ofReal p) μ + ENNReal.ofReal (ε / 2) := by
            gcongr
            · exact (eLpNorm_indicator_le _).trans
                (eLpNorm_condExp_le_eLpNorm_ofReal (h𝒢 i) hp (f - fun x ↦ g x))
            · exact hUIgδ i s hs hμs
      _ ≤ ENNReal.ofReal ε := by
            have hfg' : eLpNorm (f - (fun x ↦ g x)) (ENNReal.ofReal p) μ ≤
                ENNReal.ofReal (ε / 2) := hfg.le
            calc
              _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hfg' le_rfl
              _ = ENNReal.ofReal ε := by
                rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]
  · refine ⟨(eLpNorm f (ENNReal.ofReal p) μ).toNNReal, fun i ↦ ?_⟩
    calc
      eLpNorm μ[f | 𝒢 i] (ENNReal.ofReal p) μ
          ≤ eLpNorm f (ENNReal.ofReal p) μ :=
        eLpNorm_condExp_le_eLpNorm_ofReal (h𝒢 i) hp f
      _ = ↑(eLpNorm f (ENNReal.ofReal p) μ).toNNReal :=
        (ENNReal.coe_toNNReal hf.eLpNorm_ne_top).symm

end AdvancedProbability
