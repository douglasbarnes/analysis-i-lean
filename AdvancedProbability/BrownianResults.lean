import AdvancedProbability.BrownianMotion
import AdvancedProbability.BrownianBasicImported

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u

open ProbabilityTheory

/-- Source 89, in the native Gaussian-covariance formulation: a standard real Brownian motion is a
centred Gaussian process with covariance `min s t` and almost-surely continuous paths. -/
abbrev IsStandardBrownianReal {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsBrownianReal B P

/-- Source 91: every standard Brownian motion is a Gaussian process. -/
theorem BrownianGaussianProcessTheorem {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P) :
    IsGaussianProcess B P :=
  hB.isGaussianProcess

/-- Every one-time Brownian marginal is Gaussian. -/
theorem BrownianHasGaussianLawEval {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P) (t : ℝ≥0) :
    ProbabilityTheory.HasGaussianLaw (B t) P :=
  hB.isGaussianProcess.hasGaussianLaw_eval t

/-- Every Brownian increment is Gaussian. -/
theorem BrownianIncrementHasGaussianLaw {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P)
    (s t : ℝ≥0) :
    ProbabilityTheory.HasGaussianLaw (B s - B t) P :=
  hB.isGaussianProcess.hasGaussianLaw_sub

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

/-- Source 92(d): time inversion preserves the pre-Brownian Gaussian covariance data. -/
theorem BrownianTimeInversionFiniteDimensional {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P) :
    IsPreBrownianReal (fun t ω ↦ t * B (1 / t) ω) P :=
  hB.inv

/-- Source 92: reflection, scaling, deterministic translation, and time inversion. -/
theorem BrownianInvarianceTheorem {Ω : Type u} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P) :
    IsBrownianReal (-B) P ∧
      (∀ c : ℝ≥0, c ≠ 0 →
        IsBrownianReal (fun t ω ↦ (√c)⁻¹ * B (c * t) ω) P) ∧
      (∀ t₀ : ℝ≥0,
        IsBrownianReal (fun t ω ↦ B (t₀ + t) ω - B t₀ ω) P) ∧
      IsPreBrownianReal (fun t ω ↦ t * B (1 / t) ω) P := by
  refine ⟨hB.neg, ?_, ?_, hB.inv⟩
  · intro c hc
    exact hB.smul hc
  · intro t₀
    exact hB.shift t₀

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
