import AdvancedProbability.LpLevyUpwardResults
import AdvancedProbability.LpMartingaleResults
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section

open scoped ENNReal NNReal Topology MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory ProbabilityTheory

namespace AdvancedProbability

universe u v

/-- Uniform integrability is inherited from an indexed dominating family. -/
theorem uniformIntegrable_of_dominated_local
    {Ω : Type u} [MeasurableSpace Ω] {ι κ : Type v} {μ : Measure Ω}
    {X : ι → Ω → ℝ} {Y : κ → Ω → ℝ} {q : ℝ≥0∞}
    (hY : UniformIntegrable Y q μ)
    (mX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hX : ∀ i, ∃ j, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ ‖Y j ω‖) :
    UniformIntegrable X q μ := by
  refine ⟨mX, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, h⟩ := hY.2.1 hε
    refine ⟨δ, hδ, fun i s hs hμs ↦ ?_⟩
    obtain ⟨j, hj⟩ := hX i
    refine (eLpNorm_mono_ae ?_).trans (h j s hs hμs)
    filter_upwards [hj] with ω hω
    by_cases hmem : ω ∈ s <;> simp [Set.indicator, hmem, hω]
  · obtain ⟨C, hC⟩ := hY.2.2
    refine ⟨C, fun i ↦ ?_⟩
    obtain ⟨j, hj⟩ := hX i
    exact (eLpNorm_mono_ae hj).trans (hC j)

/-- A single `Lᵖ` random variable dominating a family makes that family uniformly integrable. -/
theorem uniformIntegrable_of_dominated_singleton_local
    {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} {μ : Measure Ω}
    {X : ι → Ω → ℝ} {Y : Ω → ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hqtop : q ≠ ∞) (hY : MemLp Y q μ)
    (mX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hX : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ Y ω) :
    UniformIntegrable X q μ :=
  uniformIntegrable_of_dominated_local
    (uniformIntegrable_const hq hqtop hY) mX
    (fun i ↦ ⟨i, by filter_upwards [hX i] with ω hω using hω.trans (Real.le_norm_self _)⟩)

namespace LpMartingaleConvergence

variable {Ω : Type u} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m₀} {X : ℕ → Ω → ℝ} {R : ℝ≥0}

/-- Partial running maximum of the extended norms. -/
private noncomputable def H (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (Finset.range (n + 1)).sup fun k ↦ ‖X k ω‖ₑ

/-- The all-time extended-norm envelope. -/
private noncomputable def G (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n, ‖X n ω‖ₑ

private lemma H_mono (ω : Ω) : Monotone fun n ↦ H X n ω := fun _ _ hab ↦
  Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hab 1))

private lemma G_eq_iSup_H (ω : Ω) : G X ω = ⨆ n, H X n ω := by
  refine le_antisymm (iSup_le fun n ↦ le_iSup_of_le n ?_) (iSup_le fun n ↦ ?_)
  · exact Finset.le_sup (f := fun k ↦ ‖X k ω‖ₑ) (Finset.self_mem_range_succ n)
  · exact Finset.sup_le fun k _ ↦ le_iSup (fun m ↦ ‖X m ω‖ₑ) k

private lemma measurable_H (hmeas : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (H X n) := by
  show Measurable fun ω ↦ (Finset.range (n + 1)).sup fun k ↦ ‖X k ω‖ₑ
  simp only [Finset.sup_eq_iSup]
  exact .iSup fun k ↦ .iSup fun _ ↦ (hmeas k).enorm

private lemma measurable_G (hmeas : ∀ n, Measurable (X n)) : Measurable (G X) :=
  .iSup fun n ↦ (hmeas n).enorm

private lemma H_eq_enorm_runMax (n : ℕ) (ω : Ω) :
    H X n ω = ‖(Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ ‖X k ω‖)‖ₑ := by
  refine le_antisymm (Finset.sup_le fun k hk ↦ ?_) ?_
  · rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      ((Finset.le_sup' (fun m ↦ ‖X m ω‖) hk).trans (Real.le_norm_self _))
  · obtain ⟨k₀, hk₀, heq⟩ := Finset.exists_mem_eq_sup'
      Finset.nonempty_range_add_one (fun k ↦ ‖X k ω‖)
    rw [heq, show ‖(‖X k₀ ω‖)‖ₑ = ‖X k₀ ω‖ₑ from by
      rw [← ofReal_norm, norm_norm, ofReal_norm]]
    exact Finset.le_sup (f := fun k ↦ ‖X k ω‖ₑ) hk₀

/-- Peel the finite real exponent off an `Lᵖ` seminorm. -/
private lemma lintegral_enorm_rpow (g : Ω → ℝ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ ω, ‖g ω‖ₑ ^ p ∂μ = eLpNorm g (ENNReal.ofReal p) μ ^ p := by
  have hq0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.2 hp)
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul]
  rw [show 1 / p * p = 1 by field_simp, ENNReal.rpow_one]

/-- The partial running maxima have a uniform `p`-moment bound supplied by Doob's inequality. -/
private lemma lintegral_H_rpow_le [IsFiniteMeasure μ]
    (hX : Martingale X ℱ μ) {p : ℝ} (hp : 1 < p)
    (hbdd : ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ R) (n : ℕ) :
    ∫⁻ ω, H X n ω ^ p ∂μ ≤
      (ENNReal.ofReal (p / (p - 1)) * R) ^ p := by
  have hdoob : eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one fun k ↦ ‖X k ω‖) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (p / (p - 1)) * R :=
    (hX.eLpNorm_norm_runMax_le hp n).trans (mul_le_mul_right (hbdd n) _)
  calc
    ∫⁻ ω, H X n ω ^ p ∂μ =
        eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one fun k ↦ ‖X k ω‖)
          (ENNReal.ofReal p) μ ^ p := by
      rw [← lintegral_enorm_rpow _ (zero_lt_one.trans hp)]
      exact lintegral_congr fun ω ↦ by rw [H_eq_enorm_runMax]
    _ ≤ (ENNReal.ofReal (p / (p - 1)) * R) ^ p :=
      ENNReal.rpow_le_rpow hdoob (zero_lt_one.trans hp).le

/-- Monotone convergence transfers the Doob bound to the all-time envelope. -/
private lemma lintegral_G_rpow_le [IsFiniteMeasure μ]
    (hX : Martingale X ℱ μ) (hmeas : ∀ n, Measurable (X n))
    {p : ℝ} (hp : 1 < p)
    (hbdd : ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ R) :
    ∫⁻ ω, G X ω ^ p ∂μ ≤
      (ENNReal.ofReal (p / (p - 1)) * R) ^ p := by
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  have hpt : ∀ ω, G X ω ^ p = ⨆ n, H X n ω ^ p := by
    intro ω
    have h₂ : Tendsto (fun n ↦ H X n ω ^ p) atTop
        (𝓝 ((⨆ n, H X n ω) ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp (tendsto_atTop_iSup (H_mono ω))
    have h₃ : Tendsto (fun n ↦ H X n ω ^ p) atTop
        (𝓝 (⨆ n, H X n ω ^ p)) :=
      tendsto_atTop_iSup fun a b hab ↦ ENNReal.rpow_le_rpow (H_mono ω hab) hp0
    rw [G_eq_iSup_H]
    exact tendsto_nhds_unique h₂ h₃
  calc
    ∫⁻ ω, G X ω ^ p ∂μ = ∫⁻ ω, ⨆ n, H X n ω ^ p ∂μ := lintegral_congr hpt
    _ = ⨆ n, ∫⁻ ω, H X n ω ^ p ∂μ :=
      lintegral_iSup
        (fun n ↦ ENNReal.continuous_rpow_const.measurable.comp (measurable_H hmeas n))
        (fun a b hab ω ↦ ENNReal.rpow_le_rpow (H_mono ω hab) hp0)
    _ ≤ (ENNReal.ofReal (p / (p - 1)) * R) ^ p :=
      iSup_le fun n ↦ lintegral_H_rpow_le hX hp hbdd n

/-- The all-time envelope is a real `Lᵖ` random variable dominating every martingale term. -/
private lemma exists_dominator [IsFiniteMeasure μ]
    (hX : Martingale X ℱ μ) (hmeas : ∀ n, Measurable (X n))
    {p : ℝ} (hp : 1 < p)
    (hbdd : ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ R) :
    ∃ g : Ω → ℝ, Measurable g ∧ MemLp g (ENNReal.ofReal p) μ ∧
      ∀ n, ∀ᵐ ω ∂μ, ‖X n ω‖ ≤ g ω := by
  have hp_pos : 0 < p := zero_lt_one.trans hp
  have hq0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.2 hp_pos)
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hG_ne : ∫⁻ ω, G X ω ^ p ∂μ ≠ ∞ :=
    (lt_of_le_of_lt (lintegral_G_rpow_le hX hmeas hp hbdd) (by finiteness)).ne
  have hG_fin : ∀ᵐ ω ∂μ, G X ω ^ p < ∞ :=
    ae_lt_top (ENNReal.continuous_rpow_const.measurable.comp (measurable_G hmeas)) hG_ne
  have hne : ∀ᵐ ω ∂μ, G X ω ≠ ∞ := by
    filter_upwards [hG_fin] with ω hω
    exact fun htop ↦ by simp [htop, hp_pos] at hω
  refine ⟨fun ω ↦ (G X ω).toReal, (measurable_G hmeas).ennreal_toReal, ?_, ?_⟩
  · refine ⟨(measurable_G hmeas).ennreal_toReal.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop,
      ENNReal.toReal_ofReal hp_pos.le]
    have heq : ∫⁻ ω, ‖(G X ω).toReal‖ₑ ^ p ∂μ = ∫⁻ ω, G X ω ^ p ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hne] with ω hω
      rw [← ofReal_norm, Real.norm_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hω]
    rw [heq]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hG_ne
  · intro n
    filter_upwards [hne] with ω hω
    have hmono := ENNReal.toReal_mono hω (le_iSup (fun m ↦ ‖X m ω‖ₑ) n)
    rwa [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] at hmono

end LpMartingaleConvergence

open LpMartingaleConvergence in
/-- A discrete martingale bounded in a finite real `Lᵖ`, `p > 1`, converges almost surely and in
`Lᵖ` to Mathlib's canonical limit process. -/
theorem Martingale.ae_tendsto_and_eLpNorm_tendsto_ofReal
    {Ω : Type u} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m₀} {X : ℕ → Ω → ℝ} {R : ℝ≥0}
    (hX : Martingale X ℱ μ) {p : ℝ} (hp : 1 < p)
    (hbdd : ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ R) :
    (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
      Tendsto (fun n ↦ eLpNorm (X n - ℱ.limitProcess X μ)
        (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hp_pos : 0 < p := zero_lt_one.trans hp
  have hqone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hmeas : ∀ n, Measurable (X n) := fun n ↦
    ((hX.stronglyMeasurable n).mono (ℱ.le n)).measurable
  have hbdd1 : ∃ R₁ : ℝ≥0, ∀ n, eLpNorm (X n) 1 μ ≤ (R₁ : ℝ≥0∞) := by
    set c : ℝ≥0∞ := μ Set.univ ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal) with hc
    have hc_ne : c ≠ ∞ := by
      rw [hc]
      exact (ENNReal.rpow_lt_top_of_nonneg (by
        rw [ENNReal.toReal_ofReal hp_pos.le]
        positivity) (measure_ne_top μ _)).ne
    refine ⟨((R : ℝ≥0∞) * c).toNNReal, fun n ↦ ?_⟩
    have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := μ) (p := 1) (q := ENNReal.ofReal p) hqone (hmeas n).aestronglyMeasurable
    rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hc_ne)]
    exact hcompare.trans (mul_le_mul_right (hbdd n) c)
  obtain ⟨R₁, hR₁⟩ := hbdd1
  have hae := hX.submartingale.ae_tendsto_limitProcess hR₁
  have hlimit : MemLp (ℱ.limitProcess X μ) (ENNReal.ofReal p) μ :=
    hX.submartingale.memLp_limitProcess hbdd
  obtain ⟨g, hgm, hg, hdom⟩ :=
    LpMartingaleConvergence.exists_dominator hX hmeas hp hbdd
  exact ⟨hae, tendsto_Lp_finite_of_tendsto_ae hqone hqtop
    (fun n ↦ (hmeas n).aestronglyMeasurable) hlimit
    (uniformIntegrable_of_dominated_singleton_local hqone hqtop hg
      (fun n ↦ (hmeas n).aestronglyMeasurable) hdom).unifIntegrable hae⟩

end AdvancedProbability
