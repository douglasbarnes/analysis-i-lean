import AdvancedProbability.Foundations

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory ProbabilityTheory Function
open Set Filter MeasureTheory ProbabilityTheory

namespace AdvancedProbability

universe u

/-- Source 17: the measurable/integral characterization of conditional expectation.

For an integrable real random variable `X`, an integrable `Y` is a version of `E[X | m]` exactly when
it is `m`-measurable and has the same integral as `X` over every `m`-measurable event. -/
theorem ConditionalExpectationCharacterizationTheorem
    {Ω : Type u} [m₀ : MeasurableSpace Ω] {m : MeasurableSpace Ω}
    {μ : @Measure Ω m₀} (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {X Y : Ω → ℝ} (hX : Integrable X μ) :
    Y =ᵐ[μ] μ[X | m] ↔
      AEStronglyMeasurable[m] Y μ ∧ Integrable Y μ ∧
        ∀ A : Set Ω, MeasurableSet[m] A →
          ∫ x in A, Y x ∂μ = ∫ x in A, X x ∂μ := by
  constructor
  · intro hY
    refine ⟨stronglyMeasurable_condExp.aestronglyMeasurable.congr hY.symm,
      integrable_condExp.congr hY.symm, ?_⟩
    intro A hA
    calc
      ∫ x in A, Y x ∂μ = ∫ x in A, μ[X | m] x ∂μ :=
        setIntegral_congr_ae (hm A hA) hY
      _ = ∫ x in A, X x ∂μ := setIntegral_condExp hm hX hA
  · rintro ⟨hYm, hYint, hset⟩
    exact ae_eq_condExp_of_forall_setIntegral_eq hm hX
      (fun _ _ _ ↦ hYint.integrableOn) (fun A hA _ ↦ hset A hA) hYm

/-- Source 20(1): an integrable random variable is its own conditional expectation exactly when it is
measurable with respect to the conditioning sigma-field, modulo almost-everywhere equality. -/
theorem ConditionalExpectationFixedIff {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {X : Ω → ℝ} (hX : Integrable X μ) :
    μ[X | m] =ᵐ[μ] X ↔ AEStronglyMeasurable[m] X μ := by
  constructor
  · intro h
    exact stronglyMeasurable_condExp.aestronglyMeasurable.congr h
  · intro h
    exact condExp_of_aestronglyMeasurable' hm h hX

/-- Source 20(2): conditional expectation preserves the total integral. -/
theorem ConditionalExpectationPreservesIntegral {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} (hm : m ≤ m₀)
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
    {m₁ m₂ : MeasurableSpace Ω} {μ : @Measure Ω m₀} {X : Ω → ℝ}
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

/-- Source 20(6): conditional expectations preserve an increasing integrable limit. -/
theorem ConditionalExpectationMonotoneConvergence {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {Xn : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXn_int : ∀ n, Integrable (Xn n) μ)
    (hXn_meas : ∀ n, AEStronglyMeasurable[m₀] (Xn n) μ)
    (hmono : ∀ n, Xn n ≤ᵐ[μ] Xn (n + 1))
    (hnonneg : ∀ n, 0 ≤ᵐ[μ] Xn n)
    (hle : ∀ n, Xn n ≤ᵐ[μ] X)
    (hX_int : Integrable X μ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Xn n ω) atTop (𝓝 (X ω))) :
    (∀ n, μ[Xn n | m] ≤ᵐ[μ] μ[Xn (n + 1) | m]) ∧
      Tendsto (fun n ↦ condExpL1 hm μ (Xn n)) atTop (𝓝 (condExpL1 hm μ X)) := by
  constructor
  · intro n
    exact condExp_mono (hXn_int n) (hXn_int (n + 1)) (hmono n)
  · apply tendsto_condExpL1_of_dominated_convergence hm X hXn_meas hX_int
    · intro n
      filter_upwards [hnonneg n, hle n] with ω h0 hleω
      simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hleω
    · exact hlim

/-- Source 20(8): dominated convergence for conditional expectations, expressed in `L¹`. -/
theorem ConditionalExpectationDominatedConvergence {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {Xn : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (bound : Ω → ℝ)
    (hXn_meas : ∀ n, AEStronglyMeasurable[m₀] (Xn n) μ)
    (hbound_int : Integrable bound μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ bound ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Xn n ω) atTop (𝓝 (X ω))) :
    Tendsto (fun n ↦ condExpL1 hm μ (Xn n)) atTop (𝓝 (condExpL1 hm μ X)) :=
  tendsto_condExpL1_of_dominated_convergence hm bound hXn_meas hbound_int hbound hlim

/-- Source 20(9): conditional Jensen inequality for a lower-semicontinuous convex function. -/
theorem ConditionalExpectationJensen {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {X : Ω → ℝ} {φ : ℝ → ℝ}
    (hconvex : ConvexOn ℝ Set.univ φ)
    (hlsc : LowerSemicontinuousOn φ Set.univ)
    (hX : Integrable X μ) (hφX : Integrable (φ ∘ X) μ) :
    φ ∘ μ[X | m] ≤ᵐ[μ] μ[φ ∘ X | m] := by
  exact hconvex.map_condExp_le hm hlsc (ae_of_all μ fun _ ↦ Set.mem_univ _)
    isClosed_univ hX hφX

/-- Source 20(10): the tower property. -/
theorem ConditionalExpectationTower {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {m₁ m₂ : MeasurableSpace Ω} {μ : @Measure Ω m₀} {X : Ω → ℝ}
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀) [SigmaFinite (μ.trim hm₂)] :
    μ[μ[X | m₂] | m₁] =ᵐ[μ] μ[X | m₁] :=
  condExp_condExp_of_le hm₁₂ hm₂

/-- The `L¹` contraction property available directly in the pinned Mathlib revision. -/
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
