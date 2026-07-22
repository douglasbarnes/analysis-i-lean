import ProbabilityAndMeasure.IntegralUniquenessResults
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Probability and Measure: uniform integrability

Source-numbered declarations for finite uniformly integrable families and Vitali convergence.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace ProbabilityAndMeasure

/-- Source 120, lines 3153--3157: a finite family of `L¹` functions is uniformly
integrable in the probability-theory sense (small-set control plus a uniform `L¹` bound). -/
theorem source120_finite_uniformIntegrable
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (f : ι → α → ℝ) (hf : ∀ i, MemLp (f i) 1 μ) :
    UniformIntegrable f 1 μ := by
  refine ⟨fun i ↦ (hf i).aestronglyMeasurable,
    unifIntegrable_finite (p := 1) (μ := μ) (by simp) (by simp) hf, ?_⟩
  let C : ℝ≥0 := ∑ i, (eLpNorm (f i) 1 μ).toNNReal
  refine ⟨C, fun i ↦ ?_⟩
  rw [← ENNReal.coe_toNNReal (hf i).eLpNorm_lt_top.ne]
  exact ENNReal.coe_le_coe.2
    (Finset.single_le_sum (fun j _ ↦ zero_le _) (Finset.mem_univ i))

/-- Source 121, Vitali convergence with an already identified `L¹` limit.  This is the exact
Mathlib theorem: convergence in measure together with uniform absolute continuity of the
integrals is equivalent to `L¹` convergence.  A separate source-facing theorem will remove the
explicit `MemLp g 1 μ` assumption by deriving it from Fatou's lemma. -/
theorem source121_vitali_with_integrable_limit
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 1 μ) (hg : MemLp g 1 μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f 1 μ ↔
      Tendsto (fun n ↦ eLpNorm (f n - g) 1 μ) atTop (𝓝 0) :=
  tendstoInMeasure_iff_tendsto_Lp_finite (by simp) (by simp) hf hg

end ProbabilityAndMeasure
