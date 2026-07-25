import AdvancedProbability.ContinuousTime
import Mathlib.Probability.Process.Kolmogorov

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory

namespace AdvancedProbability

universe u

/-- Mathlib's Kolmogorov moment condition specialised to real processes indexed by non-negative
real time. This is the native hypothesis underlying source 58. -/
abbrev IsRealKolmogorovProcess {Ω : Type u} [MeasurableSpace Ω]
    (X : ContinuousProcess Ω) (P : Measure Ω) (p q : ℝ) (M : ℝ≥0) : Prop :=
  ProbabilityTheory.IsKolmogorovProcess X P p q M

/-- Measurable real coordinates together with the Kolmogorov moment estimate define a real
Kolmogorov process. -/
theorem IsRealKolmogorovProcess.mk_of_measurable {Ω : Type u} [MeasurableSpace Ω]
    {X : ContinuousProcess Ω} {P : Measure Ω} {p q : ℝ} {M : ℝ≥0}
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hmoment : ∀ s t : ℝ≥0,
      ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤
        (M : ℝ≥0∞) * edist s t ^ q)
    (hp : 0 < p) (hq : 0 < q) :
    IsRealKolmogorovProcess X P p q M :=
  ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology
    hmeas hmoment hp hq

/-- Every real Kolmogorov process is, trivially, a process almost-everywhere equal at every time to
one satisfying the Kolmogorov condition. -/
theorem IsRealKolmogorovProcess.isAEKolmogorovProcess
    {Ω : Type u} [MeasurableSpace Ω] {X : ContinuousProcess Ω} {P : Measure Ω}
    {p q : ℝ} {M : ℝ≥0} (hX : IsRealKolmogorovProcess X P p q M) :
    ProbabilityTheory.IsAEKolmogorovProcess X P p q M :=
  hX.IsAEKolmogorovProcess

end AdvancedProbability