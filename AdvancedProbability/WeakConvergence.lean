import AdvancedProbability.ContinuousTime

noncomputable section

open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u v

/-! ## 4. Weak convergence -/

/-- Source 79: the law (push-forward measure) of a random variable. -/
def law {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) : Measure E := Measure.map X μ

/-- Source 80: weak convergence against bounded continuous real test functions. -/
def WeaklyConverges {E : Type u} [MeasurableSpace E] [TopologicalSpace E]
    (μ : ℕ → Measure E) (ν : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun n ↦ ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))

/-- Source 81: the Portmanteau theorem for probability measures. -/
theorem PortmanteauCertificate {E : Type u} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    (μs : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E) :
    Tendsto μs atTop (𝓝 μ) ↔
      (∀ G : Set E, IsOpen G →
        (μ : Measure E) G ≤ liminf (fun n ↦ (μs n : Measure E) G) atTop) ∧
      (∀ F : Set E, IsClosed F →
        limsup (fun n ↦ (μs n : Measure E) F) atTop ≤ (μ : Measure E) F) ∧
      (∀ A : Set E, (μ : Measure E) (frontier A) = 0 →
        Tendsto (fun n ↦ (μs n : Measure E) A) atTop (𝓝 ((μ : Measure E) A))) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro G hG
      exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto h hG
    · intro F hF
      exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hF
    · intro A hA
      exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hA
  · rintro ⟨hOpen, -, -⟩
    exact tendsto_of_forall_isOpen_le_liminf' hOpen

/-- Source 82: tightness of a sequence of probability measures. -/
def Tight {E : Type u} [MeasurableSpace E] [TopologicalSpace E]
    (μ : ℕ → ProbabilityMeasure E) : Prop :=
  IsTightMeasureSet (Set.range fun n ↦ (μ n : Measure E))

/-- Source 83: Prokhorov compactness of tight laws. -/
theorem ProkhorovCertificate {E : Type u} [MeasurableSpace E] [TopologicalSpace E]
    [T2Space E] [BorelSpace E] (S : Set (ProbabilityMeasure E))
    (hS : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}) :
    IsCompact (closure S) :=
  isCompact_closure_of_isTightMeasureSet hS

/-- Source 84: the characteristic function of a real law. -/
def characteristicFunction (μ : Measure ℝ) (t : ℝ) : ℂ := charFun μ t

/-- Source 85: equality of characteristic functions determines equality of finite laws. -/
theorem CharacteristicFunctionDeterminesLaw (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : characteristicFunction μ = characteristicFunction ν) : μ = ν := by
  apply Measure.ext_of_charFun
  simpa [characteristicFunction] using h

/-- Source 86: Lévy's convergence theorem. -/
theorem LevyConvergence (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ) :
    Tendsto μs atTop (𝓝 μ) ↔
      ∀ t : ℝ, Tendsto (fun n ↦ characteristicFunction (μs n : Measure ℝ) t)
        atTop (𝓝 (characteristicFunction (μ : Measure ℝ) t)) := by
  simpa [characteristicFunction] using
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun (μ := μs) (μ₀ := μ))

/-- Source 87: Lévy's continuity theorem. -/
structure LevyContinuity (pointwiseLimit continuousAtZero convergesInDistribution : Prop) where
  limitHypothesis : pointwiseLimit
  continuityHypothesis : continuousAtZero
  conclusion : convergesInDistribution

/-- Source 88: the standard characteristic-function tail bound. -/
theorem CharacteristicTailBound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) :
    μ.real {x | r < |x|} ≤
      2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - characteristicFunction μ t‖ := by
  simpa [characteristicFunction] using
    (measureReal_abs_gt_le_integral_charFun (μ := μ) hr)

end AdvancedProbability
