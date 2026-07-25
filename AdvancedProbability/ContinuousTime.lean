import AdvancedProbability.DiscreteMartingales
import Mathlib.Probability.Process.Filtration

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u v

/-! ## 3. Continuous-time processes -/

/-- Source 53: a real stochastic process indexed by non-negative real time. -/
abbrev ContinuousProcess (Ω : Type u) := ℝ≥0 → Ω → ℝ

/-- Source 54: right-continuous paths with left limits. -/
def IsCadlag (f : ℝ≥0 → ℝ) : Prop :=
  (∀ t, Tendsto f (nhdsWithin t (Set.Ioi t)) (𝓝 (f t))) ∧
    ∀ t, 0 < t → ∃ y, Tendsto f (nhdsWithin t (Set.Iio t)) (𝓝 y)

/-- Source 55: pathwise continuity of a stochastic process. -/
def IsContinuousProcess {Ω : Type u} (X : ContinuousProcess Ω) : Prop :=
  ∀ ω, Continuous (fun t ↦ X t ω)

/-- Source 56: continuous path space on the non-negative half-line. -/
def ContinuousPathSpace := {f : ℝ≥0 → ℝ // Continuous f}

/-- Source 57: a finite-dimensional distribution of a process. -/
def FiniteDimensionalDistribution {Ω : Type u} (X : ContinuousProcess Ω)
    (times : List ℝ≥0) : Ω → (Fin times.length → ℝ) :=
  fun ω i ↦ X (times.get i) ω

/-- Source 58: Kolmogorov's continuity criterion. -/
structure KolmogorovContinuityCriterion {Ω : Type u} (X : ContinuousProcess Ω) where
  version : ContinuousProcess Ω
  isVersion : ∀ t, X t = version t
  continuousPaths : IsContinuousProcess version

/-- Source 59: non-negative dyadic rational numbers. -/
structure Dyadic where
  numerator : ℕ
  exponent : ℕ
  value : ℚ := numerator / (2 ^ exponent : ℚ)

/-- Source 60: a filtration indexed by non-negative real time. -/
structure ContinuousFiltration (Ω : Type u) where
  sigma : ℝ≥0 → SigmaField Ω
  mono : ∀ s t : ℝ≥0, s ≤ t → (sigma s).Subfield (sigma t)

namespace SigmaField

/-- The Mathlib measurable space carried by a course-facing sigma-field. -/
@[reducible] def toMeasurableSpace {Ω : Type u} (𝒢 : SigmaField Ω) : MeasurableSpace Ω where
  MeasurableSet' := fun A ↦ A ∈ 𝒢.sets
  measurableSet_empty := 𝒢.empty_mem
  measurableSet_compl := 𝒢.compl_mem
  measurableSet_iUnion := 𝒢.iUnion_mem

@[simp] theorem measurableSet_toMeasurableSpace {Ω : Type u} (𝒢 : SigmaField Ω)
    (A : Set Ω) : @MeasurableSet Ω 𝒢.toMeasurableSpace A ↔ A ∈ 𝒢.sets :=
  Iff.rfl

end SigmaField

namespace ContinuousFiltration

/-- A course-facing continuous filtration as a Mathlib filtration of the maximal ambient measurable
space. -/
def toMathlib {Ω : Type u} (ℱ : ContinuousFiltration Ω) :
    Filtration ℝ≥0 (⊤ : MeasurableSpace Ω) where
  seq t := (ℱ.sigma t).toMeasurableSpace
  mono' := by
    intro s t hst A hA
    exact ℱ.mono s t hst hA
  le' := fun _ ↦ le_top

end ContinuousFiltration

/-- Source 61: a continuous-time stopping time. -/
def IsContinuousStoppingTime {Ω : Type u} (ℱ : ContinuousFiltration Ω)
    (T : Ω → ℝ≥0) : Prop := ∀ t, {ω | T ω ≤ t} ∈ (ℱ.sigma t).sets

/-- Source 64: an abstract first hitting time. -/
def HittingTime {Ω : Type u} (X : ContinuousProcess Ω) (A : Set ℝ) (ω : Ω) : Set ℝ≥0 :=
  {t | X t ω ∈ A}

/-- Source 65: closed-set hitting times of continuous paths are stopping times. -/
structure ClosedSetHittingTime (isClosed continuousPaths stopping : Prop) where
  closedHypothesis : isClosed
  continuousHypothesis : continuousPaths
  conclusion : stopping

/-- Source 66: the canonical right continuation `F_{t+}` of a continuous filtration. -/
noncomputable def rightContinuousFiltration {Ω : Type u} (ℱ : ContinuousFiltration Ω) :
    Filtration ℝ≥0 (⊤ : MeasurableSpace Ω) :=
  ℱ.toMathlib.rightCont

/-- On non-negative real time, the right-continuous filtration at `t` is the infimum of all
sigma-algebras strictly after `t`. -/
theorem rightContinuousFiltration_apply {Ω : Type u} (ℱ : ContinuousFiltration Ω) (t : ℝ≥0) :
    rightContinuousFiltration ℱ t = ⨅ s > t, ℱ.toMathlib s := by
  change ℱ.toMathlib.rightCont t = _
  exact Filtration.rightCont_eq ℱ.toMathlib t

/-- The canonical right continuation is right-continuous. -/
instance rightContinuousFiltration_isRightContinuous {Ω : Type u} (ℱ : ContinuousFiltration Ω) :
    Filtration.IsRightContinuous (rightContinuousFiltration ℱ) := by
  unfold rightContinuousFiltration
  infer_instance

/-- Source 67: completeness and right-continuity (the usual conditions). -/
structure UsualConditions {Ω : Type u} (ℱ : ContinuousFiltration Ω) where
  complete : Prop
  rightContinuous : Prop

/-- Source 68: open-set hitting times are stopping times for the right-continuous filtration. -/
structure OpenSetHittingTime (isOpen cadlag stopping : Prop) where
  openHypothesis : isOpen
  cadlagHypothesis : cadlag
  conclusion : stopping

/-- Source 69: a continuous-time martingale. -/
def IsContinuousTimeMartingale {Ω : Type u} (expectation : Expectation Ω)
    (CE : SigmaField Ω → (Ω → ℝ) → Ω → ℝ) (ℱ : ContinuousFiltration Ω)
    (X : ContinuousProcess Ω) : Prop :=
  (∀ t, Observable (ℱ.sigma t) (X t)) ∧
    (∀ t, IntegrableFor expectation (X t)) ∧
    ∀ s t, s ≤ t → CE (ℱ.sigma s) (X t) = X s

/-- Source 70: bounded continuous-time optional stopping. -/
structure ContinuousOptionalStoppingBounded {Ω : Type u} (expectation : Expectation Ω)
    (X : ContinuousProcess Ω) (S T : Ω → ℝ≥0) where
  order : ∀ ω, S ω ≤ T ω
  conclusion : Prop

/-- Source 71: almost-sure convergence of an `L¹`-bounded continuous supermartingale. -/
structure ContinuousSupermartingaleConvergence {Ω : Type u} (X : ContinuousProcess Ω) where
  limit : Ω → ℝ
  convergence : ∀ ω, Tendsto (fun n : ℕ ↦ X (n : ℝ≥0) ω) atTop (𝓝 (limit ω))

/-- Source 72: continuous-time maximal inequality. -/
structure ContinuousMaximalInequality (threshold probability expectationValue : ℝ) where
  threshold_pos : 0 < threshold
  estimate : threshold * probability ≤ expectationValue

/-- Source 73: continuous-time Doob `Lᵖ` inequality. -/
structure ContinuousDoobLpInequality (p maxNorm terminalNorm : ℝ) where
  p_gt_one : 1 < p
  estimate : maxNorm ≤ p / (p - 1) * terminalNorm

/-- Source 74: equality of one-time marginals (a version of a process). -/
def IsVersion {Ω : Type u} (X Y : ContinuousProcess Ω) : Prop := ∀ t, X t = Y t

/-- Source 75: right-limit regularization of martingales. -/
structure MartingaleRegularization {Ω : Type u} (X : ContinuousProcess Ω) where
  regularized : ContinuousProcess Ω
  version : IsVersion X regularized
  cadlag : ∀ ω, IsCadlag (fun t ↦ regularized t ω)

/-- Source 76: continuous-time `Lᵖ` martingale convergence. -/
structure ContinuousLpMartingaleConvergence {Ω : Type u} (X : ContinuousProcess Ω) where
  limit : Ω → ℝ
  pointwise : ∀ ω, Tendsto (fun n : ℕ ↦ X (n : ℝ≥0) ω) atTop (𝓝 (limit ω))
  normConvergence : Prop

/-- Source 77: continuous-time `L¹` martingale convergence. -/
structure ContinuousL1MartingaleConvergence (uniformIntegrable terminalRepresentation convergesL1 : Prop) where
  ui_iff_terminal : uniformIntegrable ↔ terminalRepresentation
  terminal_iff_converges : terminalRepresentation ↔ convergesL1

/-- Source 78: optional stopping for uniformly integrable continuous martingales. -/
structure ContinuousUIOptionalStopping (conditionalIdentity expectationIdentity : Prop) where
  conditional : conditionalIdentity
  expectation : expectationIdentity

end AdvancedProbability
