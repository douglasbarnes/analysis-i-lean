import AdvancedProbability.Foundations

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory ProbabilityTheory Function
open Set Filter MeasureTheory ProbabilityTheory

namespace AdvancedProbability

universe u

/-- The thirteen conditional-expectation laws used throughout the course.  Unlike the earlier
course-facing interface, every field below is a concrete Mathlib proposition. -/
structure ConditionalExpectationLawPackage {Ω : Type u} [m₀ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (μ : Measure Ω) (X Y : Ω → ℝ) where
  measurable : StronglyMeasurable[m] (μ[X | m])
  integrable : Integrable (μ[X | m]) μ
  fixed_of_measurable : StronglyMeasurable[m] X → μ[X | m] = X
  preserves_integral : ∫ ω, μ[X | m] ω ∂μ = ∫ ω, X ω ∂μ
  nonnegative : 0 ≤ᵐ[μ] X → 0 ≤ᵐ[μ] μ[X | m]
  monotone : X ≤ᵐ[μ] Y → μ[X | m] ≤ᵐ[μ] μ[Y | m]
  additive : μ[X + Y | m] =ᵐ[μ] μ[X | m] + μ[Y | m]
  homogeneous : ∀ a : ℝ, μ[a • X | m] =ᵐ[μ] a • μ[X | m]
  tower : ∀ m₁ : MeasurableSpace Ω, m₁ ≤ m → μ[μ[X | m] | m₁] =ᵐ[μ] μ[X | m₁]
  pull_out : ∀ Z : Ω → ℝ, AEStronglyMeasurable[m] Z μ → Integrable (Z * X) μ →
    μ[Z * X | m] =ᵐ[μ] Z * μ[X | m]
  independent_information : ∀ m₁ : MeasurableSpace Ω, m₁ ≤ m₀ →
    StronglyMeasurable[m₁] X → Indep m₁ m μ →
      μ[X | m] =ᵐ[μ] fun _ ↦ ∫ ω, X ω ∂μ
  abs_le : |μ[X | m]| ≤ᵐ[μ] μ[|X| | m]
  l1_contraction : eLpNorm (μ[X | m]) 1 μ ≤ eLpNorm X 1 μ

/-- Source 20: the thirteen standard conditional-expectation identities, proved for Mathlib's
conditional expectation. -/
theorem ConditionalExpectationLawsTheorem {Ω : Type u} [m₀ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (μ : Measure Ω) (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ) :
    ConditionalExpectationLawPackage m μ X Y := by
  refine
    { measurable := stronglyMeasurable_condExp
      integrable := integrable_condExp
      fixed_of_measurable := fun hXm ↦ condExp_of_stronglyMeasurable hm hXm hX
      preserves_integral := integral_condExp hm
      nonnegative := fun hnonneg ↦ condExp_nonneg hnonneg
      monotone := fun hXY ↦ condExp_mono hX hY hXY
      additive := condExp_add hX hY m
      homogeneous := fun a ↦ condExp_smul a X m
      tower := ?_
      pull_out := ?_
      independent_information := ?_
      abs_le := abs_condExp_ae_le_condExp_abs X
      l1_contraction := eLpNorm_condExp_le_eLpNorm X le_rfl }
  · intro m₁ hm₁
    exact condExp_condExp_of_le hm₁ hm
  · intro Z hZm hZX
    exact condExp_mul_of_aestronglyMeasurable_left hZm hZX hX
  · intro m₁ hm₁ hXm hindep
    exact condExp_indep_eq hm₁ hm hXm hindep

end AdvancedProbability
