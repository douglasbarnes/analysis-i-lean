import AdvancedProbability.ContinuousTime

noncomputable section

open scoped MeasureTheory NNReal
open Filter MeasureTheory

namespace AdvancedProbability

universe u

namespace IsVersion

/-- Coordinatewise almost-sure equality of two process versions implies almost-sure equality of every
finite-dimensional random vector. -/
theorem finiteDimensionalDistribution_ae_eq {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : ContinuousProcess Ω} (hXY : IsVersion P X Y)
    (times : List ℝ≥0) :
    FiniteDimensionalDistribution X times =ᵐ[P]
      FiniteDimensionalDistribution Y times := by
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin times.length,
      X (times.get i) ω = Y (times.get i) ω := by
    rw [Filter.eventually_all]
    intro i
    exact hXY (times.get i)
  filter_upwards [hall] with ω hω
  funext i
  exact hω i

/-- A strongly adapted version of a martingale is again a martingale. -/
theorem martingale {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ}
    {ℱ : Filtration ℝ≥0 mΩ} {X Y : ContinuousProcess Ω}
    (hX : Martingale X ℱ P) (hY : StronglyAdapted ℱ Y) (hXY : IsVersion P X Y) :
    Martingale Y ℱ P :=
  hX.congr hY hXY

end IsVersion

end AdvancedProbability