import AdvancedProbability.Foundations

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory ProbabilityTheory Function
open Set Filter MeasureTheory ProbabilityTheory

namespace AdvancedProbability

universe u

/-- Source 20(1): an integrable random variable is its own conditional expectation exactly when it is
measurable with respect to the conditioning sigma-field, modulo almost-everywhere equality. -/
theorem ConditionalExpectationFixedIff {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : Measure Ω} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {X : Ω → ℝ} (hX : Integrable X μ) :
    μ[X | m] =ᵐ[μ] X ↔ AEStronglyMeasurable[m] X μ := by
  constructor
  · intro h
    exact stronglyMeasurable_condExp.aestronglyMeasurable.congr h
  · intro h
    exact condExp_of_aestronglyMeasurable' hm h hX

/-- Source 20(2): conditional expectation preserves the total integral. -/
theorem ConditionalExpectationPreservesIntegral {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : Measure Ω} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] (X : Ω → ℝ) :
    ∫ ω, μ[X | m] ω ∂μ = ∫ ω, X ω ∂μ :=
  integral_condExp hm

/-- Source 20(3): conditional expectation preserves non-negativity. -/
theorem ConditionalExpectationNonnegative {Ω : Type u} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}
    (hX : 0 ≤ᵐ[μ] X) : 0 ≤ᵐ[μ] μ[X | m] :=
  condExp_nonneg hX

/-- Source 20(4): conditioning a measurable random variable on an independent sigma-field gives its
unconditional expectation. -/
theorem ConditionalExpectationIndependent {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m₁ m₂ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}
    (hm₁ : m₁ ≤ m₀) (hm₂ : m₂ ≤ m₀) [SigmaFinite (μ.trim hm₂)]
    (hX : StronglyMeasurable[m₁] X) (hindep : Indep m₁ m₂ μ) :
    μ[X | m₂] =ᵐ[μ] fun _ ↦ ∫ ω, X ω ∂μ :=
  condExp_indep_eq hm₁ hm₂ hX hindep

/-- Source 20(5): conditional expectation is linear. -/
theorem ConditionalExpectationLinear {Ω : Type u} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) (a b : ℝ) :
    μ[a • X + b • Y | m] =ᵐ[μ] a • μ[X | m] + b • μ[Y | m] := by
  exact (condExp_add (hX.smul a) (hY.smul b) m).trans
    ((condExp_smul a X m).add (condExp_smul b Y m))

/-- Source 20(9): conditional Jensen inequality for a lower-semicontinuous convex function. -/
theorem ConditionalExpectationJensen {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : Measure Ω} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {X : Ω → ℝ} {φ : ℝ → ℝ}
    (hconvex : ConvexOn ℝ Set.univ φ)
    (hlsc : LowerSemicontinuousOn φ Set.univ)
    (hX : Integrable X μ) (hφX : Integrable (φ ∘ X) μ) :
    φ ∘ μ[X | m] ≤ᵐ[μ] μ[φ ∘ X | m] := by
  exact hconvex.map_condExp_le hm hlsc (ae_of_all μ fun _ ↦ Set.mem_univ _) isClosed_univ hX hφX

/-- Source 20(10): the tower property. -/
theorem ConditionalExpectationTower {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m₁ m₂ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀) [SigmaFinite (μ.trim hm₂)] :
    μ[μ[X | m₂] | m₁] =ᵐ[μ] μ[X | m₁] :=
  condExp_condExp_of_le hm₁₂ hm₂

/-- Source 20(11), the `p = 1` case: conditional expectation is an `L¹` contraction. -/
theorem ConditionalExpectationL1Contraction {Ω : Type u} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : Measure Ω} (X : Ω → ℝ) :
    eLpNorm (μ[X | m]) 1 μ ≤ eLpNorm X 1 μ :=
  eLpNorm_one_condExp_le_eLpNorm X

/-- Source 20(12): a measurable factor can be pulled out of conditional expectation. -/
theorem ConditionalExpectationPullOut {Ω : Type u} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : Measure Ω} {Z X : Ω → ℝ}
    (hZ : AEStronglyMeasurable[m] Z μ)
    (hZX : Integrable (Z * X) μ) (hX : Integrable X μ) :
    μ[Z * X | m] =ᵐ[μ] Z * μ[X | m] :=
  condExp_mul_of_aestronglyMeasurable_left hZ hZX hX

end AdvancedProbability
