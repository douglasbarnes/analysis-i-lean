import AdvancedProbability.Foundations

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory ProbabilityTheory Function
open Set Filter MeasureTheory ProbabilityTheory

namespace AdvancedProbability

universe u

/-- A concrete package of the conditional-expectation laws currently available in the pinned
Mathlib revision. -/
structure ConditionalExpectationLawPackage {Ω : Type u} [m₀ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (μ : @Measure Ω m₀) (X Y : Ω → ℝ) where
  measurable : StronglyMeasurable[m] (MeasureTheory.condExp m μ X)
  integrable : Integrable (MeasureTheory.condExp m μ X) μ
  fixed_of_measurable : StronglyMeasurable[m] X → MeasureTheory.condExp m μ X = X
  preserves_integral :
    ∫ ω, MeasureTheory.condExp m μ X ω ∂μ = ∫ ω, X ω ∂μ
  nonnegative : 0 ≤ᵐ[μ] X → 0 ≤ᵐ[μ] MeasureTheory.condExp m μ X
  monotone : X ≤ᵐ[μ] Y →
    MeasureTheory.condExp m μ X ≤ᵐ[μ] MeasureTheory.condExp m μ Y
  additive : MeasureTheory.condExp m μ (X + Y) =ᵐ[μ]
    MeasureTheory.condExp m μ X + MeasureTheory.condExp m μ Y
  homogeneous : ∀ a : ℝ, MeasureTheory.condExp m μ (a • X) =ᵐ[μ]
    a • MeasureTheory.condExp m μ X
  tower : ∀ m₁ : MeasurableSpace Ω, m₁ ≤ m →
    MeasureTheory.condExp m₁ μ (MeasureTheory.condExp m μ X) =ᵐ[μ]
      MeasureTheory.condExp m₁ μ X
  pull_out : ∀ Z : Ω → ℝ, AEStronglyMeasurable[m] Z μ → Integrable (Z * X) μ →
    MeasureTheory.condExp m μ (Z * X) =ᵐ[μ]
      Z * MeasureTheory.condExp m μ X
  independent : ∀ m₁ : MeasurableSpace Ω, m₁ ≤ m₀ →
    StronglyMeasurable[m₁] X → Indep m₁ m μ →
      MeasureTheory.condExp m μ X =ᵐ[μ] (fun _ ↦ ∫ ω, X ω ∂μ)
  abs_le : (fun ω ↦ |MeasureTheory.condExp m μ X ω|) ≤ᵐ[μ]
    MeasureTheory.condExp m μ (fun ω ↦ |X ω|)
  l1_contraction : eLpNorm (MeasureTheory.condExp m μ X) 1 μ ≤ eLpNorm X 1 μ

/-- A proved package of the standard elementary conditional-expectation laws. -/
theorem ConditionalExpectationLawsTheorem {Ω : Type u} [m₀ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (μ : @Measure Ω m₀) (hm : m ≤ m₀)
    (hSigma : @MeasureTheory.SigmaFinite Ω m (@Measure.trim Ω m m₀ μ hm))
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ) :
    ConditionalExpectationLawPackage m μ X Y := by
  letI : @MeasureTheory.SigmaFinite Ω m (@Measure.trim Ω m m₀ μ hm) := hSigma
  exact
    { measurable := stronglyMeasurable_condExp
      integrable := integrable_condExp
      fixed_of_measurable := fun hXm ↦
        condExp_of_stronglyMeasurable (μ := μ) hm hXm hX
      preserves_integral := integral_condExp (μ := μ) (m := m) (f := X) hm
      nonnegative := fun hnonneg ↦ condExp_nonneg hnonneg
      monotone := fun hXY ↦ condExp_mono hX hY hXY
      additive := condExp_add hX hY m
      homogeneous := fun a ↦ condExp_smul a X m
      tower := fun m₁ hm₁ ↦ condExp_condExp_of_le hm₁ hm
      pull_out := fun Z hZm hZX ↦
        condExp_mul_of_aestronglyMeasurable_left hZm hZX hX
      independent := fun m₁ hm₁ hXm hindep ↦
        condExp_indep_eq hm₁ hm hXm hindep
      abs_le := abs_condExp_ae_le_condExp_abs X
      l1_contraction := eLpNorm_one_condExp_le_eLpNorm X }

end AdvancedProbability
