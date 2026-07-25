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
  rw [Metric.tendstoUniformly_iff] at hF hG ⊢
  intro ε hε
  let D : ℝ := 2 * (|a| + |b| + 1)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  filter_upwards [hF (ε / D) (div_pos hε hD), hG (ε / D) (div_pos hε hD)]
    with n hFn hGn
  intro x
  simp only [Real.dist_eq] at hFn hGn ⊢
  have hFle : |F n x - f x| ≤ ε / D := by
    simpa [abs_sub_comm] using (hFn x).le
  have hGle : |G n x - g x| ≤ ε / D := by
    simpa [abs_sub_comm] using (hGn x).le
  calc
    |(a * f x + b * g x) - (a * F n x + b * G n x)| =
        |a * (f x - F n x) + b * (g x - G n x)| := by ring_nf
    _ ≤ |a| * |f x - F n x| + |b| * |g x - G n x| := by
      simpa [abs_mul] using abs_add (a * (f x - F n x)) (b * (g x - G n x))
    _ ≤ |a| * (ε / D) + |b| * (ε / D) := by
      gcongr <;> simpa [abs_sub_comm]
    _ = (|a| + |b|) * ε / D := by ring
    _ < ε := by
      apply (div_lt_iff₀ hD).2
      dsimp [D]
      nlinarith [abs_nonneg a, abs_nonneg b]

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
