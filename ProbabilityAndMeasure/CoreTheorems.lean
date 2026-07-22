import ProbabilityAndMeasure.TransformsAndLimits
import Mathlib.Probability.BorelCantelli

/-!
# Probability and Measure: source theorem wrappers

Named theorem-level declarations for the main results in the lecture notes. The statements expose
Mathlib's actual hypotheses rather than replacing the results by assumptions.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory Function

namespace ProbabilityAndMeasure

/-! ## Measures -/

/-- Source line 117: sigma-algebras are closed under countable intersections. -/
theorem measurableSet_iInter_source {α ι : Type*} [MeasurableSpace α]
    [Countable ι] (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableSet (⋂ i, A i) :=
  MeasurableSet.iInter hA

/-- Source lines 117--128: countable additivity of an existing measure. -/
theorem measure_iUnion_disjoint_source {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n))
    (hdis : Pairwise (Function.onFun Disjoint A)) :
    μ (⋃ n, A n) = ∑' n, μ (A n) :=
  measure_iUnion hdis hA

/-- Continuity from above for decreasing measurable sets of finite initial mass. -/
theorem measure_continuous_iInter_source {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : ℕ → Set α) (hA : ∀ n, NullMeasurableSet (A n) μ)
    (hanti : Antitone A) (hfin : ∃ n, μ (A n) ≠ ∞) :
    Tendsto (fun n ↦ μ (A n)) atTop (𝓝 (μ (⋂ n, A n))) := by
  simpa [Function.comp_def] using
    tendsto_measure_iInter_atTop (μ := μ) hA hanti hfin

/-- Source line 724: the first Borel--Cantelli lemma. -/
theorem borelCantelli_one_source {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : ℕ → Set α) (hsum : (∑' n, μ (A n)) ≠ ∞) :
    μ (limsup A atTop) = 0 :=
  MeasureTheory.measure_limsup_atTop_eq_zero hsum

/-- Source line 747: the second Borel--Cantelli lemma. -/
theorem borelCantelli_two_source {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (hind : ProbabilityTheory.iIndepSet A P) (hsum : (∑' n, P (A n)) = ∞) :
    P (limsup A atTop) = 1 :=
  ProbabilityTheory.measure_limsup_eq_one hA hind hsum

/-! ## Measurable functions and laws -/

/-- Source line 852: composition of measurable functions is measurable. -/
theorem measurable_comp_source {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α → β} {g : β → γ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (g ∘ f) :=
  hg.comp hf

/-- Source lines 967 and 1084: evaluation of the law on a measurable event. -/
theorem law_apply_source {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (X : Ω → S) (hX : Measurable X)
    (A : Set S) (hA : MeasurableSet A) :
    law P X A = P (X ⁻¹' A) := by
  simpa [law] using Measure.map_apply hX hA

/-- Source line 1096: a cumulative distribution function is monotone. -/
theorem cdf_monotone_source {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : Monotone (cdf P X) := by
  intro x y hxy
  apply measure_mono
  intro ω hω
  exact hω.trans hxy

/-- Source line 882: a measurable product-valued function has measurable coordinates. -/
theorem coordinate_measurable_source {Ω ι : Type*} [MeasurableSpace Ω]
    {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (X : Ω → ∀ i, S i) (hX : Measurable X) (i : ι) :
    Measurable (fun ω ↦ X ω i) :=
  (measurable_pi_apply i).comp hX

/-! ## Integration and limits -/

/-- Source line 1677: monotone convergence for non-negative extended-real functions. -/
theorem monotone_convergence_source {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (htendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, F x ∂μ)) :=
  lintegral_tendsto_of_tendsto_of_monotone hf hmono htendsto

/-- Source line 1892: the integral of a countable sum of non-negative measurable functions is the
sum of the integrals. -/
theorem lintegral_tsum_source {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) {f : ι → α → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) μ) :
    (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ :=
  lintegral_tsum hf

/-- Source line 1926: Fatou's lemma. -/
theorem fatou_source {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, liminf (fun n ↦ f n x) atTop ∂μ) ≤
      liminf (fun n ↦ ∫⁻ x, f n x ∂μ) atTop :=
  lintegral_liminf_le hf

/-- Source line 1987: dominated convergence for non-negative extended-real functions. -/
theorem dominated_convergence_source {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF : ∀ n, Measurable (F n))
    (hbound : ∀ n, F n ≤ᵐ[μ] bound) (hfin : ∫⁻ x, bound x ∂μ ≠ ∞)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ ∫⁻ x, F n x ∂μ) atTop (𝓝 (∫⁻ x, f x ∂μ)) :=
  tendsto_lintegral_of_dominated_convergence bound hF hbound hfin hlim

/-- Source integration section: linearity for two integrable Bochner-integrable functions. -/
theorem integral_add_source' {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (f g : α → E) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, f x + g x ∂μ) = (∫ x, f x ∂μ) + ∫ x, g x ∂μ :=
  integral_add hf hg

/-! ## Inequalities and Hilbert-space identities -/

/-- Source line 2700: the standard two-term power estimate used in Minkowski's inequality. -/
theorem add_rpow_bound_source (a b : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (a + b) ^ p ≤ (2 : ℝ≥0) ^ (p - 1) * (a ^ p + b ^ p) :=
  NNReal.rpow_add_le_mul_rpow_add_rpow a b hp

/-- Source line 2909: expansion of the squared norm in a real inner-product space. -/
theorem pythagoras_source {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + 2 * inner ℝ x y := by
  calc
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x y + ‖y‖ ^ 2 := norm_add_sq_real x y
    _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 + 2 * inner ℝ x y := by ring

/-- Source line 2915: the parallelogram law. -/
theorem parallelogram_source {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
  parallelogram_law_with_norm ℝ x y

end ProbabilityAndMeasure
