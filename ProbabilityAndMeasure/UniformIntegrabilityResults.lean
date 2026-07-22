import ProbabilityAndMeasure.IntegralUniquenessResults
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Probability and Measure: uniform integrability

Source-numbered declarations for closure, tail control, finite uniformly integrable families, and
Vitali convergence.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace ProbabilityAndMeasure

/-- Source 117, binary union step: the disjoint-index union of two uniformly integrable
families is uniformly integrable.  Iterating this result gives closure under finite unions. -/
theorem source117_uniformIntegrable_sum
    {α ι κ E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞}
    {f : ι → α → E} {g : κ → α → E}
    (hf : UniformIntegrable f p μ) (hg : UniformIntegrable g p μ) :
    UniformIntegrable (Sum.elim f g) p μ := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    cases z with
    | inl i => exact hf.1 i
    | inr j => exact hg.1 j
  · intro ε hε
    obtain ⟨δf, hδf, hfδ⟩ := hf.2.1 hε
    obtain ⟨δg, hδg, hgδ⟩ := hg.2.1 hε
    refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
    intro z A hA hμA
    cases z with
    | inl i =>
        exact hfδ i A hA
          (hμA.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    | inr j =>
        exact hgδ j A hA
          (hμA.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  · obtain ⟨Cf, hCf⟩ := hf.2.2
    obtain ⟨Cg, hCg⟩ := hg.2.2
    refine ⟨max Cf Cg, ?_⟩
    intro z
    cases z with
    | inl i => exact (hCf i).trans (ENNReal.coe_le_coe.2 (le_max_left _ _))
    | inr j => exact (hCg j).trans (ENNReal.coe_le_coe.2 (le_max_right _ _))

/-- Source 119, lines 3123--3129: uniform integrability is equivalent to uniform decay of
the `L¹` mass above a common truncation level.  This is Mathlib's exact probability-theory
characterisation. -/
theorem source119_uniformIntegrable_iff_tail
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ι → α → ℝ} :
    UniformIntegrable f 1 μ ↔
      (∀ i, AEStronglyMeasurable (f i) μ) ∧
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
          ∀ i, eLpNorm ({x | C ≤ ‖f i x‖₊}.indicator (f i)) 1 μ ≤ ENNReal.ofReal ε :=
  uniformIntegrable_iff (p := 1) (by simp) (by simp)

/-- Source 120, lines 3153--3157: a finite family of `L¹` functions is uniformly
integrable in the probability-theory sense. -/
theorem source120_finite_uniformIntegrable
    {α ι : Type*} [MeasurableSpace α] [Finite ι]
    (μ : Measure α) (f : ι → α → ℝ) (hf : ∀ i, MemLp (f i) 1 μ) :
    UniformIntegrable f 1 μ :=
  uniformIntegrable_finite (p := 1) (μ := μ) (by simp) (by simp) hf

/-- Source 121, Vitali convergence with an already identified `L¹` limit.  This is the exact
Mathlib theorem: convergence in measure together with uniform absolute continuity of the
integrals is equivalent to `L¹` convergence.  The separate full source theorem must additionally
package the uniform norm bound in the forward direction and derive `MemLp g 1 μ` in the reverse
direction. -/
theorem source121_vitali_with_integrable_limit
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 1 μ) (hg : MemLp g 1 μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f 1 μ ↔
      Tendsto (fun n ↦ eLpNorm (f n - g) 1 μ) atTop (𝓝 0) :=
  tendstoInMeasure_iff_tendsto_Lp_finite (by simp) (by simp) hf hg

/-- The difficult reverse implication in source 121, without assuming in advance that the
limit is integrable: uniform integrability and convergence in probability imply that the limit
belongs to `L¹`. -/
theorem source121_limit_integrable_of_UI_and_probability
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hUI : UniformIntegrable f 1 μ) (hprob : TendstoInMeasure μ f atTop g) :
    MemLp g 1 μ :=
  hUI.memLp_of_tendstoInMeasure hprob

end ProbabilityAndMeasure
