import AdvancedProbability.BrownianMotion
import Mathlib.Dynamics.Ergodic.MeasurePreserving

noncomputable section

open scoped NNReal
open Set MeasureTheory

namespace AdvancedProbability

universe u

/-- The event that a real process reaches level `b` by time `t` and finishes at or below `a`. -/
def BrownianHitBelowEvent {Ω : Type u} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (b a : ℝ) : Set Ω :=
  {ω | (∃ s : ℝ≥0, s ≤ t ∧ b ≤ B s ω) ∧ B t ω ≤ a}

/-- A terminal upper-tail event for a real process. -/
def BrownianUpperTailEvent {Ω : Type u} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (c : ℝ) : Set Ω :=
  {ω | c ≤ B t ω}

/-- Source 98: the first-passage reflection identity as the direct measure-theoretic corollary of the
reflection principle.

For the reflection map at the first hitting time of `b`, the source-97 reflection principle supplies
`hR`. Pathwise reflection supplies `hReflects`; under the usual hypotheses `0 < b` and `a ≤ b`, it
identifies the preimage of the terminal event `{B t ≥ 2b-a}` with
`{sup_{s ≤ t} B s ≥ b, B t ≤ a}`. -/
theorem ReflectionHittingIdentityTheorem
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a b : ℝ) {R : Ω → Ω}
    (hR : MeasurePreserving R μ μ)
    (hTail : MeasurableSet (BrownianUpperTailEvent B t (2 * b - a)))
    (hReflects : R ⁻¹' BrownianUpperTailEvent B t (2 * b - a) =
      BrownianHitBelowEvent B t b a) :
    μ (BrownianHitBelowEvent B t b a) =
      μ (BrownianUpperTailEvent B t (2 * b - a)) := by
  rw [← hReflects]
  exact hR.measure_preimage hTail.nullMeasurableSet

end AdvancedProbability
