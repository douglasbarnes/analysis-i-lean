import AdvancedProbability.BrownianMotion
import Mathlib.Probability.Independence.ZeroOne

noncomputable section

open MeasureTheory ProbabilityTheory

namespace AdvancedProbability

universe u

/-- Source 94: Blumenthal's zero-one conclusion follows once the Brownian germ sigma-algebra is
independent of itself.

The remaining Brownian-specific dependency is to derive `hself` from future-increment independence
at the right-limit filtration. This theorem formalizes the exact zero-one mechanism after that
independence statement has been established. -/
theorem BlumenthalZeroOneTheorem
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (germ : MeasurableSpace Ω) (hself : Indep germ germ μ) :
    ∀ A : Set Ω, MeasurableSet[germ] A → μ A = 0 ∨ μ A = 1 := by
  intro A hA
  exact ProbabilityTheory.measure_eq_zero_or_one_of_indepSet_self
    (hself A A hA hA)

end AdvancedProbability
