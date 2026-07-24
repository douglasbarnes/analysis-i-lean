import AdvancedProbability.BrownianMotion
import AdvancedProbability.BrownianBasicImported

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u

open ProbabilityTheory

/-- Source 89, in the native Mathlib formulation: a standard real Brownian motion is a process with
the canonical Brownian finite-dimensional laws and almost-surely continuous paths. -/
abbrev IsStandardBrownianReal {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsBrownianReal B P

/-- Source 91: every standard Brownian motion is a Gaussian process. -/
theorem BrownianGaussianProcessTheorem {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P) :
    IsGaussianProcess B P :=
  hB.isGaussianProcess

/-- The one-time Brownian marginal is the centered Gaussian law of variance `t`. -/
theorem BrownianHasLawEval {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P) (t : ℝ≥0) :
    HasLaw (B t) (gaussianReal 0 t) P :=
  hB.hasLaw_eval t

/-- Brownian increments are centered Gaussian with variance equal to the elapsed time. -/
theorem BrownianHasLawIncrement {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P)
    (s t : ℝ≥0) :
    HasLaw (B s - B t) (gaussianReal 0 (nndist s.1 t.1)) P :=
  hB.hasLaw_sub s t

/-- Brownian motion has independent increments. -/
theorem BrownianHasIndependentIncrements {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P) :
    HasIndepIncrements B P :=
  hB.hasIndepIncrements

/-- Source 92(a): reflection in the spatial origin preserves Brownian motion. -/
theorem BrownianReflectionInvariance {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P) :
    IsBrownianReal (-B) P :=
  hB.neg

/-- Source 92(b): Brownian scaling. -/
theorem BrownianScalingInvariance {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P)
    {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianReal (fun t ω ↦ (√c)⁻¹ * B (c * t) ω) P :=
  hB.smul hc

/-- Source 92(c): deterministic time shifts, recentered at the shift time, preserve Brownian motion. -/
theorem BrownianTranslationInvariance {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P)
    (t₀ : ℝ≥0) :
    IsBrownianReal (fun t ω ↦ B (t₀ + t) ω - B t₀ ω) P :=
  hB.shift t₀

/-- Source 92(d), law-level time inversion: `t ↦ t B_{1/t}` has the Brownian
finite-dimensional distributions.  Continuity at zero is the only additional pathwise assertion
needed to upgrade this to `IsBrownianReal`. -/
theorem BrownianTimeInversionFiniteDimensional {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P) :
    IsPreBrownianReal (fun t ω ↦ t * B (1 / t) ω) P :=
  hB.inv

/-- Source 93 at deterministic time for the natural past: future increments form a pre-Brownian
motion independent of all Brownian coordinates up to the shift time. -/
theorem BrownianFutureIndependentNaturalPast {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P)
    (t₀ : ℝ≥0) :
    IsPreBrownianReal (fun t ω ↦ B (t₀ + t) ω - B t₀ ω) P ∧
      IndepFun (fun ω t ↦ B (t₀ + t) ω - B t₀ ω)
        (fun ω (t : Set.Iic t₀) ↦ B t ω) P :=
  ⟨hB.toIsPreBrownianReal.shift t₀, hB.indepFun_shift t₀⟩

end AdvancedProbability
