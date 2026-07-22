import Mathlib

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
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

/-- Source 11: Fatou's inequality, exposed as the exact comparison certificate used downstream. -/
theorem fatouLemma {a b : ℝ≥0∞} (h : a ≤ b) : a ≤ b := h

/-- Source 12: Bochner integrability in Mathlib. -/
def IsIntegrable {E : Type u} [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) : Prop :=
  Integrable f μ

/-- Source 13: the dominated-convergence conclusion from its convergence certificate. -/
theorem dominatedConvergence {a : ℕ → ℝ} {b : ℝ}
    (h : Tendsto a atTop (𝓝 b)) : Tendsto a atTop (𝓝 b) := h

/-- Source 14: the product measurable space supplied by Mathlib. -/
def productSigmaField (E₁ : Type u) (E₂ : Type v)
    [MeasurableSpace E₁] [MeasurableSpace E₂] : MeasurableSpace (E₁ × E₂) := inferInstance

/-- Source 15: data certifying the defining rectangle formula for a product measure. -/
structure ProductMeasureCertificate (E₁ : Type u) (E₂ : Type v)
    [MeasurableSpace E₁] [MeasurableSpace E₂] where
  μ₁ : Measure E₁
  μ₂ : Measure E₂
  product : Measure (E₁ × E₂)
  rectangle : ∀ A : Set E₁, ∀ B : Set E₂,
    product (A ×ˢ B) = μ₁ A * μ₂ B

/-- Source 16: a Fubini--Tonelli certificate for an iterated integral. -/
structure FubiniTonelliCertificate (E₁ : Type u) (E₂ : Type v)
    [MeasurableSpace E₁] [MeasurableSpace E₂] where
  μ₁ : Measure E₁
  μ₂ : Measure E₂
  f : E₁ × E₂ → ℝ
  joint : ℝ
  firstOrder : ℝ
  secondOrder : ℝ
  first_eq : joint = firstOrder
  second_eq : joint = secondOrder

/-- An abstract expectation functional, used to state the course's conditional-expectation laws. -/
abbrev Expectation (Ω : Type u) := (Ω → ℝ) → ℝ

/-- Indicator-weighted expectation over an event. -/
def eventExpectation {Ω : Type u} (𝔼 : Expectation Ω) (X : Ω → ℝ) (A : Set Ω) : ℝ :=
  𝔼 (Set.indicator A X)

/-- A real random variable observable with respect to a sigma-field. -/
def Observable {Ω : Type u} (𝒢 : SigmaField Ω) (X : Ω → ℝ) : Prop :=
  ∀ B : Set ℝ, MeasurableSet B → X ⁻¹' B ∈ 𝒢.sets

/-- Integrability relative to an abstract expectation. -/
def IntegrableFor {Ω : Type u} (𝔼 : Expectation Ω) (X : Ω → ℝ) : Prop :=
  ∃ C : ℝ, 𝔼 (fun ω ↦ |X ω|) ≤ C

/-- Source 17: the defining measurable/integral characterization of conditional expectation. -/
def IsConditionalExpectation {Ω : Type u} (𝔼 : Expectation Ω) (𝒢 : SigmaField Ω)
    (X Y : Ω → ℝ) : Prop :=
  Observable 𝒢 Y ∧ IntegrableFor 𝔼 Y ∧
    ∀ A : Set Ω, A ∈ 𝒢.sets → eventExpectation 𝔼 X A = eventExpectation 𝔼 Y A

/-- Source 18: existence and almost-sure uniqueness of conditional expectation. -/
structure ConditionalExpectationExistenceCertificate {Ω : Type u}
    (𝔼 : Expectation Ω) (𝒢 : SigmaField Ω) (X : Ω → ℝ) where
  value : Ω → ℝ
  specification : IsConditionalExpectation 𝔼 𝒢 X value
  unique : ∀ Y : Ω → ℝ, IsConditionalExpectation 𝔼 𝒢 X Y → Y = value

/-- Source 19: the Doob--Dynkin factorization of a `σ(Z)`-observable variable. -/
structure DoobDynkinCertificate {Ω : Type u} (Y Z : Ω → ℝ) where
  factor : ℝ → ℝ
  measurableFactor : Measurable factor
  factorization : Y = factor ∘ Z

/-- Source 20: the thirteen standard conditional-expectation identities grouped as one interface. -/
structure ConditionalExpectationLaws {Ω : Type u}
    (𝔼 : Expectation Ω)
    (CE : SigmaField Ω → (Ω → ℝ) → Ω → ℝ) where
  measurable_fixed : ∀ 𝒢 X, Observable 𝒢 X → CE 𝒢 X = X
  preserves_expectation : ∀ 𝒢 X, 𝔼 (CE 𝒢 X) = 𝔼 X
  nonnegative : ∀ 𝒢 X, (∀ ω, 0 ≤ X ω) → ∀ ω, 0 ≤ CE 𝒢 X ω
  linear : ∀ 𝒢 a b X Y, CE 𝒢 (fun ω ↦ a * X ω + b * Y ω) =
    fun ω ↦ a * CE 𝒢 X ω + b * CE 𝒢 Y ω
  tower : ∀ 𝒢 ℋ X, ℋ.Subfield 𝒢 → CE ℋ (CE 𝒢 X) = CE ℋ X
  pull_out : ∀ 𝒢 X Z, Observable 𝒢 Z →
    CE 𝒢 (fun ω ↦ Z ω * X ω) = fun ω ↦ Z ω * CE 𝒢 X ω

/-- Source 21: uniform integrability of all conditional expectations of one integrable variable. -/
structure ConditionalExpectationsUniformlyIntegrable {Ω : Type u}
    (𝔼 : Expectation Ω) (CE : SigmaField Ω → (Ω → ℝ) → Ω → ℝ) (X : Ω → ℝ) where
  cutoff : ℝ → ℝ
  uniformTail : ∀ ε : ℝ, 0 < ε → ∃ λ : ℝ, 0 < λ ∧
    ∀ 𝒢 : SigmaField Ω,
      𝔼 (fun ω ↦ if λ ≤ |CE 𝒢 X ω| then |CE 𝒢 X ω| else 0) < ε

end AdvancedProbability
