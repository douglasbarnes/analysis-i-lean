import AdvancedProbability.Foundations

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory ProbabilityTheory

namespace AdvancedProbability

universe u

/-- Conditional expectation of an extended non-negative random variable, represented by the
regular conditional probability kernel.  This is the correct version for variables which need not
be integrable. -/
def nonnegativeConditionalExpectation {Ω : Type u} [m₀ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (m : MeasurableSpace Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ≥0∞) : Ω → ℝ≥0∞ :=
  fun ω ↦ ∫⁻ x, X x ∂condExpKernel μ m ω

/-- Source 20(7): conditional Fatou's lemma.  It holds pointwise for the canonical regular
conditional-probability version, hence in particular almost surely. -/
theorem ConditionalExpectationFatou {Ω : Type u} [m₀ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (m : MeasurableSpace Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable (X n)) :
    nonnegativeConditionalExpectation m μ (fun ω ↦ liminf (fun n ↦ X n ω) atTop) ≤
      fun ω ↦ liminf (fun n ↦ nonnegativeConditionalExpectation m μ (X n) ω) atTop := by
  intro ω
  exact lintegral_liminf_le hX

/-- Conditional monotone convergence for extended non-negative random variables. -/
theorem ConditionalExpectationMonotoneConvergenceENNReal {Ω : Type u}
    [m₀ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (m : MeasurableSpace Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable (X n))
    (hmono : Monotone X) :
    nonnegativeConditionalExpectation m μ (fun ω ↦ ⨆ n, X n ω) =
      fun ω ↦ ⨆ n, nonnegativeConditionalExpectation m μ (X n) ω := by
  funext ω
  exact lintegral_iSup hX hmono

end AdvancedProbability
