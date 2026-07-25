import AdvancedProbability.ReflectionCorollaryResults
import Mathlib.Probability.CDF

noncomputable section

open scoped NNReal ENNReal
open Set MeasureTheory ProbabilityTheory

namespace AdvancedProbability

universe u

/-- Source 99: a non-negative running maximum has the same law as the absolute terminal position once
reflection and symmetry identify all of their positive upper tails.

For Brownian motion, `hMaxTail` is the `a ↑ b` consequence of source 98 and `hAbsTail` is the
symmetry of the centred Gaussian terminal law.  The proof below performs the remaining measure
extension step, including the non-positive thresholds. -/
theorem RunningMaximumLawTheorem
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M X : Ω → ℝ) (hM : Measurable M) (hX : Measurable X)
    (hMnonneg : ∀ ω, 0 ≤ M ω)
    (hMaxTail : ∀ b : ℝ, 0 < b →
      μ {ω | b ≤ M ω} = 2 * μ {ω | b ≤ X ω})
    (hAbsTail : ∀ b : ℝ, 0 < b →
      μ {ω | b ≤ |X ω|} = 2 * μ {ω | b ≤ X ω}) :
    ProbabilityTheory.HasLaw M (μ.map fun ω ↦ |X ω|) μ := by
  have hAbs : Measurable (fun ω ↦ |X ω|) := hX.abs
  refine ⟨hM.aemeasurable, ?_⟩
  apply Measure.ext_of_Ici
  intro a
  rw [Measure.map_apply hM measurableSet_Ici,
    Measure.map_apply hAbs measurableSet_Ici]
  change μ {ω | a ≤ M ω} = μ {ω | a ≤ |X ω|}
  by_cases ha : 0 < a
  · exact (hMaxTail a ha).trans (hAbsTail a ha).symm
  · have ha0 : a ≤ 0 := le_of_not_gt ha
    have hMset : {ω | a ≤ M ω} = (Set.univ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ha0.trans (hMnonneg ω)
    have hAbsSet : {ω | a ≤ |X ω|} = (Set.univ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ha0.trans (abs_nonneg _)
    rw [hMset, hAbsSet]

end AdvancedProbability
