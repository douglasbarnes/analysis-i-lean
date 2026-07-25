import AdvancedProbability.Foundations

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory ProbabilityTheory

namespace AdvancedProbability

universe u

/-- Conditional expectation of an extended non-negative random variable, represented by the
regular conditional probability kernel. -/
def nonnegativeConditionalExpectation {Ω : Type u} [m₀ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (m : MeasurableSpace Ω) (μ : @Measure Ω m₀)
    [IsFiniteMeasure μ] (X : Ω → ℝ≥0∞) : Ω → ℝ≥0∞ :=
  fun ω ↦ ∫⁻ x, X x ∂ProbabilityTheory.condExpKernel (mΩ := m₀) μ m ω

/-- Source 20(7): conditional Fatou's lemma for the canonical regular conditional-probability
version of non-negative conditional expectation. -/
theorem ConditionalExpectationFatou {Ω : Type u} [m₀ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (m : MeasurableSpace Ω) (μ : @Measure Ω m₀)
    [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ≥0∞)
    (hX : ∀ n, Measurable[m₀] (X n)) :
    nonnegativeConditionalExpectation (m₀ := m₀) m μ
        (fun ω ↦ liminf (fun n ↦ X n ω) atTop) ≤
      fun ω ↦ liminf
        (fun n ↦ nonnegativeConditionalExpectation (m₀ := m₀) m μ (X n) ω) atTop := by
  intro ω
  exact lintegral_liminf_le hX

/-- Conditional monotone convergence for extended non-negative random variables. -/
theorem ConditionalExpectationMonotoneConvergenceENNReal {Ω : Type u}
    [m₀ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (m : MeasurableSpace Ω) (μ : @Measure Ω m₀) [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable[m₀] (X n))
    (hmono : Monotone X) :
    nonnegativeConditionalExpectation (m₀ := m₀) m μ (fun ω ↦ ⨆ n, X n ω) =
      fun ω ↦ ⨆ n, nonnegativeConditionalExpectation (m₀ := m₀) m μ (X n) ω := by
  funext ω
  exact lintegral_iSup hX hmono

end AdvancedProbability
