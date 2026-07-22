import ProbabilityAndMeasure.RandomVariables

/-!
# Probability and Measure: integration

Simple functions, the Bochner/Lebesgue integral, expectation, moments, restrictions,
pushforwards, densities, product measures, and uniform integrability.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace ProbabilityAndMeasure

/-- A non-negative real simple function, in the elementary form used in the notes. -/
def IsSimpleFunction {α : Type*} [MeasurableSpace α] (f : α → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (Set.range f).Finite

/-- The Bochner integral. -/
def integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (f : α → E) : E :=
  ∫ x, f x ∂μ

/-- Expectation is integration against a probability measure. -/
def expectation {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (X : Ω → E) : E :=
  ∫ ω, X ω ∂P

/-- The `r`th real moment. -/
def moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (r : ℕ) : ℝ :=
  ∫ ω, X ω ^ r ∂P

/-- Variance as the second centered moment. -/
def variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω - expectation P X) ^ 2 ∂P

/-- Covariance of two real random variables. -/
def covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω - expectation P X) * (Y ω - expectation P Y) ∂P

/-- The real indicator of an event. -/
noncomputable def indicator {Ω : Type*} (A : Set Ω) (ω : Ω) : ℝ :=
  Set.indicator A (fun _ ↦ 1) ω

/-- Restriction of a measure to a measurable subset. -/
def restrictMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : Set α) : Measure α :=
  μ.restrict A

/-- Pushforward (image) measure. -/
def pushforward {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) : Measure β :=
  μ.map f

/-- A measure specified by an extended non-negative density. -/
def densityMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ≥0∞) : Measure α :=
  μ.withDensity f

/-- Product measure. -/
def productMeasure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) : Measure (α × β) :=
  μ.prod ν

/-- Linearity of the integral for integrable functions. -/
theorem integral_add_source {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (f g : α → E)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    integral μ (fun x ↦ f x + g x) = integral μ f + integral μ g := by
  simpa [integral] using MeasureTheory.integral_add hf hg

/-- Variance is non-negative. -/
theorem variance_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : 0 ≤ variance P X := by
  exact integral_nonneg fun _ ↦ sq_nonneg _

/-- Covariance is symmetric. -/
theorem covariance_comm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) : covariance P X Y = covariance P Y X := by
  simp only [covariance, mul_comm]

/-- Elementary indicator identities. -/
theorem indicator_identities {Ω : Type*} (A B : Set Ω) (ω : Ω) :
    indicator Aᶜ ω = 1 - indicator A ω ∧
      indicator (A ∩ B) ω = indicator A ω * indicator B ω ∧
      indicator (A ∪ B) ω =
        indicator A ω + indicator B ω - indicator A ω * indicator B ω := by
  classical
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
    simp [indicator, Set.indicator, hA, hB]

/-- Expectation of a product of independent integrable real random variables. -/
theorem expectation_mul_of_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X Y : Ω → ℝ)
    (hXY : ProbabilityTheory.IndepFun X Y P)
    (hX : Integrable X P) (hY : Integrable Y P) :
    expectation P (fun ω ↦ X ω * Y ω) = expectation P X * expectation P Y := by
  simpa [expectation] using
    hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable

/-- Uniform integrability in the small-set formulation, with uniform `L¹` boundedness. -/
def UniformlyIntegrable {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ) : Prop :=
  (∀ i, Integrable (X i) P) ∧
    (∃ C : ℝ, ∀ i, ∫ ω, |X i ω| ∂P ≤ C) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ i A, MeasurableSet A →
      P A < ENNReal.ofReal δ → ∫ ω in A, |X i ω| ∂P < ε

end ProbabilityAndMeasure
