import AdvancedProbability.Foundations

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory ProbabilityTheory Function
open Set Filter MeasureTheory ProbabilityTheory

namespace AdvancedProbability

universe u

/-- Source 8: existence and uniqueness of the non-negative integral.

The lower Lebesgue integral is the unique functional whose value on an arbitrary `ℝ≥0∞`-valued
function is the supremum of the integrals of all measurable simple functions dominated by it. -/
theorem NonnegativeIntegralExistenceUniqueness {E : Type u} [MeasurableSpace E]
    (μ : Measure E) :
    ∃! I : (E → ℝ≥0∞) → ℝ≥0∞,
      ∀ f : E → ℝ≥0∞,
        I f = ⨆ (g : MeasureTheory.SimpleFunc E ℝ≥0∞) (_ : ⇑g ≤ f), g.lintegral μ := by
  refine ⟨fun f ↦ nonnegativeIntegral μ f, ?_, ?_⟩
  · intro f
    change (∫⁻ x, f x ∂μ) = _
    rw [MeasureTheory.lintegral]
  · intro I hI
    funext f
    rw [hI f]
    change (⨆ (g : MeasureTheory.SimpleFunc E ℝ≥0∞) (_ : ⇑g ≤ f), g.lintegral μ) =
      ∫⁻ x, f x ∂μ
    rw [MeasureTheory.lintegral]

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
    (μ : @Measure Ω m₀) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ)
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) :
    @ConditionalExpectationLawPackage Ω m₀ m μ X Y := by
  letI : MeasurableSpace Ω := m₀
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
      abs_le := by
        have hpos := condExp_mono (m := m) hX hX.abs
          (ae_of_all μ fun ω ↦ le_abs_self (X ω))
        have hneg := condExp_mono (m := m) hX.neg hX.abs
          (ae_of_all μ fun ω ↦ neg_le_abs (X ω))
        filter_upwards [hpos, hneg, condExp_neg X m] with ω h₁ h₂ h₃
        exact abs_le'.2 ⟨h₁, h₃.symm.le.trans h₂⟩
      l1_contraction := eLpNorm_one_condExp_le_eLpNorm X }

end AdvancedProbability
