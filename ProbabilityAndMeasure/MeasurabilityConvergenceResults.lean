import ProbabilityAndMeasure.CoreTheorems
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Probability and Measure: measurability, distributions, and convergence

Source-numbered declarations for the measurable-function and convergence chapters of
`II_M/probability_and_measure.tex`.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory MeasurableSpace

namespace ProbabilityAndMeasure

/-- Source 37, lines 802--804: it suffices to test preimages of a generating family. -/
theorem source037_measurable_generateFrom {α β : Type*} [MeasurableSpace α]
    (Q : Set (Set β)) (f : α → β)
    (h : ∀ s ∈ Q, MeasurableSet (f ⁻¹' s)) :
    @Measurable α β _ (MeasurableSpace.generateFrom Q) f :=
  measurable_generateFrom h

/-- Source 40, lines 880--882: a function into a product is measurable exactly when all
coordinates are measurable. -/
theorem source040_measurable_pi_iff {α ι : Type*} [MeasurableSpace α]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (f : α → ∀ i, X i) :
    Measurable f ↔ ∀ i, Measurable (fun x ↦ f x i) :=
  measurable_pi_iff

/-- Source 49, lines 1094--1104: a cumulative distribution function is monotone,
right-continuous, and has the correct limits at both ends of the real line. -/
theorem source049_cdf_properties (μ : Measure ℝ) :
    Monotone (ProbabilityTheory.cdf μ) ∧
      (∀ x, ContinuousWithinAt (ProbabilityTheory.cdf μ) (Set.Ici x) x) ∧
      Tendsto (ProbabilityTheory.cdf μ) atBot (𝓝 0) ∧
      Tendsto (ProbabilityTheory.cdf μ) atTop (𝓝 1) := by
  exact ⟨ProbabilityTheory.monotone_cdf μ,
    fun x ↦ (ProbabilityTheory.cdf μ).right_continuous x,
    ProbabilityTheory.tendsto_cdf_atBot μ,
    ProbabilityTheory.tendsto_cdf_atTop μ⟩

/-- Source 51, lines 1119--1121: every distribution function is the cdf of a probability
measure (and hence of the identity random variable on that probability space). -/
theorem source051_realize_distribution_function (F : StieltjesFunction ℝ)
    (h0 : Tendsto F atBot (𝓝 0)) (h1 : Tendsto F atTop (𝓝 1)) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ProbabilityTheory.cdf μ = F := by
  letI : IsProbabilityMeasure F.measure := by
    refine ⟨?_⟩
    rw [F.measure_univ h0 h1, sub_zero, ENNReal.ofReal_one]
  exact ⟨F.measure, inferInstance,
    ProbabilityTheory.cdf_measure_stieltjesFunction F h0 h1⟩

/-- Source 58(i), lines 1290--1295: almost-everywhere convergence implies convergence in
measure on a finite measure space. -/
theorem source058_tendstoInMeasure_of_tendsto_ae {α E : Type*}
    [MeasurableSpace α] [PseudoEMetricSpace E] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℕ → α → E} {g : α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    TendstoInMeasure μ f atTop g :=
  tendstoInMeasure_of_tendsto_ae hf hfg

/-- Source 58(ii), lines 1290--1295: convergence in measure admits an almost-everywhere
convergent subsequence. -/
theorem source058_exists_subsequence_tendsto_ae {α E : Type*}
    [MeasurableSpace α] [PseudoEMetricSpace E] {μ : Measure α}
    {f : ℕ → α → E} {g : α → E} (hfg : TendstoInMeasure μ f atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun n ↦ f (ns n) x) atTop (𝓝 (g x)) :=
  hfg.exists_seq_tendsto_ae

/-- Source 64, lines 1606--1608: the elementary characterization of a non-negative real
simple function used in the notes. -/
theorem source064_simple_function_iff {α : Type*} [MeasurableSpace α] (f : α → ℝ) :
    IsSimpleFunction f ↔ Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (Set.range f).Finite :=
  Iff.rfl

/-- Source 72, lines 1890--1895: the integral of a countable sum of non-negative
measurable functions is the sum of their integrals. -/
theorem source072_lintegral_tsum {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) {f : ι → α → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) μ) :
    (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ :=
  lintegral_tsum hf

/-- Source 73, lines 1924--1929: Fatou's lemma. -/
theorem source073_fatou {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, liminf (fun n ↦ f n x) atTop ∂μ) ≤
      liminf (fun n ↦ ∫⁻ x, f n x ∂μ) atTop :=
  lintegral_liminf_le hf

/-- Source 76, lines 2059--2061: restriction produces a measure on the same measurable
space. -/
theorem source076_restrict_is_measure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : Set α) : ∃ ν : Measure α, ν = μ.restrict A :=
  ⟨μ.restrict A, rfl⟩

/-- Source 77, lines 2075--2077: restriction of a measurable function to a measurable
subspace is measurable. -/
theorem source077_restrict_measurable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {A : Set α} {f : α → β}
    (hf : Measurable f) : Measurable (fun x : A ↦ f x) :=
  hf.comp measurable_subtype_coe

/-- Source 78, lines 2087--2089: an integrable function remains integrable under measure
restriction, and its integral is the set integral. -/
theorem source078_restrict_integrable {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} (A : Set α)
    {f : α → E} (hf : Integrable f μ) :
    Integrable f (μ.restrict A) ∧
      (∫ x, f x ∂(μ.restrict A)) = ∫ x in A, f x ∂μ := by
  exact ⟨hf.integrableOn, rfl⟩

/-- Source 80, lines 2113--2118: integration against a pushforward measure is integration
of the pullback. -/
theorem source080_lintegral_map {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {f : α → β} (hf : Measurable f) {g : β → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ y, g y ∂μ.map f) = ∫⁻ x, g (f x) ∂μ :=
  lintegral_map hg hf

/-- Source 82, lines 2133--2135: the pushforward construction is a measure. -/
theorem source082_pushforward_is_measure {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (f : α → β) :
    ∃ ν : Measure β, ν = μ.map f :=
  ⟨μ.map f, rfl⟩

/-- Source 92, lines 2505--2510: Markov's inequality for non-negative extended-real
functions. -/
theorem source092_markov {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    μ {x | ε ≤ f x} ≤ (∫⁻ x, f x ∂μ) / ε :=
  meas_ge_le_lintegral_div hf hε0 hεtop

end ProbabilityAndMeasure
