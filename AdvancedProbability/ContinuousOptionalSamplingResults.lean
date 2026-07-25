import AdvancedProbability.ContinuousTime
import Mathlib.Probability.Martingale.OptionalSampling

noncomputable section

open scoped MeasureTheory NNReal
open Set MeasureTheory

namespace AdvancedProbability

universe u

/-- The bounded continuous-time optional-sampling identity when the two stopping times have countable
range. This is the exact theorem used for dyadic approximations in the proof of source 70. -/
theorem ContinuousOptionalStoppingCountableRange
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {X : ContinuousProcess Ω}
    (hX : IsContinuousTimeMartingale P ℱ X)
    {S T : Ω → WithTop ℝ≥0} (hS : IsStoppingTime ℱ S) (hT : IsStoppingTime ℱ T)
    (hST : S ≤ T) {N : ℝ≥0} (hTbdd : ∀ ω, T ω ≤ N)
    (hTcount : (Set.range T).Countable) (hScount : (Set.range S).Countable) :
    stoppedValue X S =ᵐ[P] P[stoppedValue X T | hS.measurableSpace] := by
  exact hX.stoppedValue_ae_eq_condExp_of_le_of_countable_range
    hT hS hST hTbdd hTcount hScount

/-- Under the same countable-range hypotheses, bounded optional sampling preserves expectation. -/
theorem ContinuousOptionalStoppingCountableRange_integral
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {X : ContinuousProcess Ω}
    (hX : IsContinuousTimeMartingale P ℱ X)
    {S T : Ω → WithTop ℝ≥0} (hS : IsStoppingTime ℱ S) (hT : IsStoppingTime ℱ T)
    (hST : S ≤ T) {N : ℝ≥0} (hTbdd : ∀ ω, T ω ≤ N)
    (hTcount : (Set.range T).Countable) (hScount : (Set.range S).Countable) :
    ∫ ω, stoppedValue X S ω ∂P = ∫ ω, stoppedValue X T ω ∂P := by
  have hcond := ContinuousOptionalStoppingCountableRange hX hS hT hST hTbdd hTcount hScount
  calc
    ∫ ω, stoppedValue X S ω ∂P =
        ∫ ω, P[stoppedValue X T | hS.measurableSpace] ω ∂P :=
      integral_congr_ae hcond
    _ = ∫ ω, stoppedValue X T ω ∂P := integral_condExp hS.measurableSpace_le

end AdvancedProbability