import Mathlib

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u v

/-! ## 1. Measure theory and conditional expectation -/

/-- Source 1: a sigma-field on `Ω`, written as a family of sets with the three closure laws. -/
structure SigmaField (Ω : Type u) where
  sets : Set (Set Ω)
  empty_mem : (∅ : Set Ω) ∈ sets
  compl_mem : ∀ A : Set Ω, A ∈ sets → Aᶜ ∈ sets
  iUnion_mem : ∀ A : ℕ → Set Ω, (∀ n, A n ∈ sets) → (⋃ n, A n) ∈ sets

/-- Inclusion of sigma-fields. -/
def SigmaField.Subfield {Ω : Type u} (𝒢 ℱ : SigmaField Ω) : Prop := 𝒢.sets ⊆ ℱ.sets

/-- Source 2: a measurable space is a carrier equipped with a sigma-field. -/
abbrev MeasurableSpaceObject (Ω : Type u) := SigmaField Ω

/-- Source 3: the Borel sigma-field is the least sigma-field containing the open sets. -/
def IsBorelSigmaField (E : Type u) [TopologicalSpace E] (𝓑 : SigmaField E) : Prop :=
  (∀ U : Set E, IsOpen U → U ∈ 𝓑.sets) ∧
    ∀ 𝒢 : SigmaField E, (∀ U : Set E, IsOpen U → U ∈ 𝒢.sets) → 𝓑.Subfield 𝒢

/-- Source 4: Mathlib's countably additive extended non-negative measure. -/
abbrev MeasureObject (Ω : Type u) [MeasurableSpace Ω] := Measure Ω

/-- Source 5: a measurable carrier together with a measure. -/
structure MeasureSpaceObject (Ω : Type u) [MeasurableSpace Ω] where
  measure : Measure Ω

/-- Source 6: measurability between two Mathlib measurable spaces. -/
def IsMeasurableMap {E₁ : Type u} {E₂ : Type v} [MeasurableSpace E₁] [MeasurableSpace E₂]
    (f : E₁ → E₂) : Prop := Measurable f

/-- Source 7: the two spaces denoted `m𝓔` and `m𝓔⁺` in the notes. -/
abbrev MeasurableFunctionNotation (E : Type u) [MeasurableSpace E] :=
  {f : E → ℝ // Measurable f} × {f : E → ℝ≥0∞ // Measurable f}

/-- Source 8: integration of a non-negative measurable function is Mathlib's `lintegral`. -/
def nonnegativeIntegral {E : Type u} [MeasurableSpace E] (μ : Measure E) (f : E → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, f x ∂μ

/-- Source 9: Mathlib's measurable simple functions. -/
abbrev SimpleFunction (E : Type u) [MeasurableSpace E] := MeasureTheory.SimpleFunc E ℝ≥0∞

/-- Source 10: equality almost everywhere with respect to a measure. -/
def AlmostEverywhereEqual {E : Type u} [MeasurableSpace E] (μ : Measure E)
    (f g : E → ℝ) : Prop := f =ᵐ[μ] g

/-- Source 11: Fatou's lemma for non-negative measurable functions. -/
theorem fatouLemma {E : Type u} [MeasurableSpace E] (μ : Measure E)
    (f : ℕ → E → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) :
    ∫⁻ x, liminf (fun n ↦ f n x) atTop ∂μ ≤
      liminf (fun n ↦ ∫⁻ x, f n x ∂μ) atTop :=
  lintegral_liminf_le hf

/-- Source 12: Bochner integrability in Mathlib. -/
def IsIntegrable {E : Type u} [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) : Prop :=
  Integrable f μ

/-- Source 13: the Bochner dominated convergence theorem. -/
theorem dominatedConvergence {E : Type u} {G : Type v} [MeasurableSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (μ : Measure E)
    {F : ℕ → E → G} {f : E → G} (bound : E → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hboundInt : Integrable bound μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hF hboundInt hbound hlim

/-- Source 14: the product measurable space supplied by Mathlib. -/
abbrev productSigmaField (E₁ : Type u) (E₂ : Type v)
    [MeasurableSpace E₁] [MeasurableSpace E₂] : MeasurableSpace (E₁ × E₂) := inferInstance

/-- Source 15: existence of the product measure and its defining rectangle formula. -/
theorem ProductMeasureCertificate {E₁ : Type u} {E₂ : Type v}
    [MeasurableSpace E₁] [MeasurableSpace E₂] (μ₁ : Measure E₁) (μ₂ : Measure E₂)
    [SFinite μ₂] (A : Set E₁) (B : Set E₂) :
    (μ₁.prod μ₂) (A ×ˢ B) = μ₁ A * μ₂ B :=
  Measure.prod_prod A B

/-- Source 16: Fubini's theorem for an integrable real-valued function. -/
theorem FubiniTonelliCertificate {E₁ : Type u} {E₂ : Type v}
    [MeasurableSpace E₁] [MeasurableSpace E₂] (μ₁ : Measure E₁) (μ₂ : Measure E₂)
    [SFinite μ₁] [SFinite μ₂] (f : E₁ × E₂ → ℝ)
    (hf : Integrable f (μ₁.prod μ₂)) :
    ∫ z, f z ∂μ₁.prod μ₂ = ∫ x, ∫ y, f (x, y) ∂μ₂ ∂μ₁ :=
  integral_prod f hf

/-- An abstract expectation functional, retained for the course-facing elementary examples. -/
abbrev Expectation (Ω : Type u) := (Ω → ℝ) → ℝ

/-- Indicator-weighted expectation over an event. -/
def eventExpectation {Ω : Type u} (expectation : Expectation Ω) (X : Ω → ℝ)
    (A : Set Ω) : ℝ := expectation (Set.indicator A X)

/-- A real random variable observable with respect to a sigma-field. -/
def Observable {Ω : Type u} (𝒢 : SigmaField Ω) (X : Ω → ℝ) : Prop :=
  ∀ B : Set ℝ, MeasurableSet B → X ⁻¹' B ∈ 𝒢.sets

/-- Integrability relative to an abstract expectation. -/
def IntegrableFor {Ω : Type u} (expectation : Expectation Ω) (X : Ω → ℝ) : Prop :=
  ∃ C : ℝ, expectation (fun ω ↦ |X ω|) ≤ C

/-- Source 17: the defining measurable/integral characterization of conditional expectation. -/
def IsConditionalExpectation {Ω : Type u} (expectation : Expectation Ω) (𝒢 : SigmaField Ω)
    (X Y : Ω → ℝ) : Prop :=
  Observable 𝒢 Y ∧ IntegrableFor expectation Y ∧
    ∀ A : Set Ω, A ∈ 𝒢.sets →
      eventExpectation expectation X A = eventExpectation expectation Y A

/-- Source 18: existence and almost-sure uniqueness of conditional expectation.

The witness is Mathlib's `condExp`; the last clause is its uniqueness characterization. -/
theorem ConditionalExpectationExistenceCertificate {Ω : Type u} [m₀ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (μ : Measure Ω) (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {X : Ω → ℝ} (hX : Integrable X μ) :
    Integrable (μ[X | m]) μ ∧
      StronglyMeasurable[m] (μ[X | m]) ∧
      (∀ A : Set Ω, MeasurableSet[m] A →
        ∫ x in A, μ[X | m] x ∂μ = ∫ x in A, X x ∂μ) ∧
      (∀ Y : Ω → ℝ, AEStronglyMeasurable[m] Y μ →
        (∀ A : Set Ω, MeasurableSet[m] A → μ A < ∞ → IntegrableOn Y A μ) →
        (∀ A : Set Ω, MeasurableSet[m] A → μ A < ∞ →
          ∫ x in A, Y x ∂μ = ∫ x in A, X x ∂μ) →
        Y =ᵐ[μ] μ[X | m]) := by
  refine ⟨integrable_condExp, stronglyMeasurable_condExp, ?_, ?_⟩
  · intro A hA
    exact setIntegral_condExp hm hX hA
  · intro Y hYm hYint hYeq
    exact ae_eq_condExp_of_forall_setIntegral_eq hm hX hYint hYeq hYm

/-- Source 19: the Doob--Dynkin factorization of a `σ(Z)`-observable variable. -/
structure DoobDynkinCertificate {Ω : Type u} (Y Z : Ω → ℝ) where
  factor : ℝ → ℝ
  measurableFactor : Measurable factor
  factorization : Y = factor ∘ Z

/-- Source 20: the thirteen standard conditional-expectation identities grouped as one interface. -/
structure ConditionalExpectationLaws {Ω : Type u}
    (expectation : Expectation Ω)
    (CE : SigmaField Ω → (Ω → ℝ) → Ω → ℝ) where
  measurable_fixed : ∀ 𝒢 X, Observable 𝒢 X → CE 𝒢 X = X
  preserves_expectation : ∀ 𝒢 X, expectation (CE 𝒢 X) = expectation X
  nonnegative : ∀ 𝒢 X, (∀ ω, 0 ≤ X ω) → ∀ ω, 0 ≤ CE 𝒢 X ω
  linear : ∀ 𝒢 a b X Y, CE 𝒢 (fun ω ↦ a * X ω + b * Y ω) =
    fun ω ↦ a * CE 𝒢 X ω + b * CE 𝒢 Y ω
  tower : ∀ 𝒢 ℋ X, ℋ.Subfield 𝒢 → CE ℋ (CE 𝒢 X) = CE ℋ X
  pull_out : ∀ 𝒢 X Z, Observable 𝒢 Z →
    CE 𝒢 (fun ω ↦ Z ω * X ω) = fun ω ↦ Z ω * CE 𝒢 X ω

/-- Source 21: all conditional expectations of one integrable real variable form a uniformly
integrable family. -/
theorem ConditionalExpectationsUniformlyIntegrable {Ω : Type u} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {ι : Type*} {X : Ω → ℝ}
    (hX : Integrable X μ) (m : ι → MeasurableSpace Ω) (hm : ∀ i, m i ≤ m₀) :
    UniformIntegrable (fun i ↦ μ[X | m i]) 1 μ :=
  hX.uniformIntegrable_condExp hm

end AdvancedProbability
