import Mathlib

open Filter Function Set Topology
open scoped Topology BigOperators

namespace AnalysisII

noncomputable section

/-- Analysis II source 1: a real-valued function sequence converges uniformly
iff it is uniformly Cauchy. -/
theorem source001_uniform_convergence_iff_uniformCauchy
    {α : Type*} (F : ℕ → α → ℝ) :
    (∃ f : α → ℝ, TendstoUniformly F f atTop) ↔
      UniformCauchySeqOn F atTop (Set.univ : Set α) := by
  constructor
  · rintro ⟨f, hf⟩
    exact hf.tendstoUniformlyOn.uniformCauchySeqOn
  · intro hF
    let f : α → ℝ := fun x =>
      Classical.choose <| cauchySeq_tendsto_of_complete
        (hF.cauchySeq (x := x) (Set.mem_univ x))
    refine ⟨f, tendstoUniformlyOn_univ.mp ?_⟩
    apply hF.tendstoUniformlyOn_of_tendsto
    intro x _
    exact Classical.choose_spec <| cauchySeq_tendsto_of_complete
      (hF.cauchySeq (x := x) (Set.mem_univ x))

/-- Analysis II source 5(i): real linear combinations preserve uniform convergence. -/
theorem source005_linear_combination
    {α : Type*} {F G : ℕ → α → ℝ} {f g : α → ℝ}
    (hF : TendstoUniformly F f atTop) (hG : TendstoUniformly G g atTop)
    (a b : ℝ) :
    TendstoUniformly
      (fun n x => a * F n x + b * G n x)
      (fun x => a * f x + b * g x) atTop := by
  have ha : TendstoUniformly (fun n x => a * F n x) (fun x => a * f x) atTop := by
    simpa [Function.comp_def] using
      (Real.uniformContinuous_const_mul (x := a)).comp_tendstoUniformly hF
  have hb : TendstoUniformly (fun n x => b * G n x) (fun x => b * g x) atTop := by
    simpa [Function.comp_def] using
      (Real.uniformContinuous_const_mul (x := b)).comp_tendstoUniformly hG
  simpa [Function.comp_def] using
    Real.uniformContinuous_add.comp_tendstoUniformly (ha.prodMk hb)

/-- Analysis II source 5(ii): multiplication by a bounded real function preserves
uniform convergence.  Boundedness is supplied by an explicit positive bound. -/
theorem source005_bounded_multiplier
    {α : Type*} {F : ℕ → α → ℝ} {f g : α → ℝ}
    (hF : TendstoUniformly F f atTop) {C : ℝ} (hC : 0 < C)
    (hg : ∀ x, |g x| ≤ C) :
    TendstoUniformly (fun n x => g x * F n x) (fun x => g x * f x) atTop := by
  rw [Metric.tendstoUniformly_iff] at hF ⊢
  intro ε hε
  filter_upwards [hF (ε / C) (div_pos hε hC)] with n hn
  intro x
  simp only [Real.dist_eq] at hn ⊢
  rw [← mul_sub, abs_mul]
  calc
    |g x| * |f x - F n x| ≤ C * |f x - F n x| :=
      mul_le_mul_of_nonneg_right (hg x) (abs_nonneg _)
    _ < C * (ε / C) := mul_lt_mul_of_pos_left (hn x) hC
    _ = ε := by field_simp [ne_of_gt hC]

/-- Analysis II source 7: Weierstrass' M-test, in a normed additive group. -/
theorem source007_weierstrass_m_test
    {α E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (g : ℕ → α → E) (M : ℕ → ℝ)
    (hM : Summable M) (hg : ∀ n x, ‖g n x‖ ≤ M n) :
    TendstoUniformly
      (fun N x => ∑ n ∈ Finset.range N, g n x)
      (fun x => ∑' n, g n x) atTop :=
  tendstoUniformly_tsum_nat hM hg

end

end AnalysisII
