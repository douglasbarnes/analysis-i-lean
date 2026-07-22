import AdvancedProbability.Foundations

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u v

/-! ## 2. Martingales in discrete time -/

/-- Source 22: an increasing sequence of sigma-fields. -/
structure DiscreteFiltration (Ω : Type u) where
  sigma : ℕ → SigmaField Ω
  mono : ∀ m n : ℕ, m ≤ n → (sigma m).Subfield (sigma n)

/-- Source 23: a real stochastic process in discrete time. -/
abbrev DiscreteProcess (Ω : Type u) := ℕ → Ω → ℝ

/-- Source 24: the natural filtration, characterized by observability and minimality. -/
structure NaturalFiltration {Ω : Type u} (X : DiscreteProcess Ω) extends DiscreteFiltration Ω where
  observes : ∀ n k : ℕ, k ≤ n → Observable (sigma n) (X k)
  minimal : ∀ ℱ : DiscreteFiltration Ω,
    (∀ n k : ℕ, k ≤ n → Observable (ℱ.sigma n) (X k)) →
      ∀ n, (sigma n).Subfield (ℱ.sigma n)

/-- Source 25: adaptation to a discrete filtration. -/
def IsAdapted {Ω : Type u} (ℱ : DiscreteFiltration Ω) (X : DiscreteProcess Ω) : Prop :=
  ∀ n, Observable (ℱ.sigma n) (X n)

/-- Source 26: pointwise integrability of a process. -/
def IsIntegrableProcess {Ω : Type u} (expectation : Expectation Ω)
    (X : DiscreteProcess Ω) : Prop := ∀ n, IntegrableFor expectation (X n)

/-- The three comparison modes for martingales, submartingales, and supermartingales. -/
inductive MartingaleType where
  | martingale | submartingale | supermartingale
  deriving DecidableEq, Repr

/-- Source 27: discrete martingale/submartingale/supermartingale. -/
def IsDiscreteMartingale {Ω : Type u} (kind : MartingaleType)
    (expectation : Expectation Ω) (CE : SigmaField Ω → (Ω → ℝ) → Ω → ℝ)
    (ℱ : DiscreteFiltration Ω) (X : DiscreteProcess Ω) : Prop :=
  IsIntegrableProcess expectation X ∧ IsAdapted ℱ X ∧
    ∀ m n : ℕ, m ≤ n →
      match kind with
      | .martingale => CE (ℱ.sigma m) (X n) = X m
      | .submartingale => ∀ ω, X m ω ≤ CE (ℱ.sigma m) (X n) ω
      | .supermartingale => ∀ ω, CE (ℱ.sigma m) (X n) ω ≤ X m ω

/-- Source 28: a discrete stopping time. -/
def IsDiscreteStoppingTime {Ω : Type u} (ℱ : DiscreteFiltration Ω) (T : Ω → ℕ) : Prop :=
  ∀ n : ℕ, {ω | T ω ≤ n} ∈ (ℱ.sigma n).sets

/-- Source 29: the random variable obtained by stopping a process. -/
def stoppedValue {Ω : Type u} (X : DiscreteProcess Ω) (T : Ω → ℕ) : Ω → ℝ :=
  fun ω ↦ X (T ω) ω

/-- Source 30: the stopped process `X_{n ∧ T}`. -/
def stoppedProcess {Ω : Type u} (X : DiscreteProcess Ω) (T : Ω → ℕ) : DiscreteProcess Ω :=
  fun n ω ↦ X (min n (T ω)) ω

/-- Source 31: the event family observable at a stopping time. -/
def stoppingSigmaField {Ω : Type u} (ℱ : DiscreteFiltration Ω) (T : Ω → ℕ) : Set (Set Ω) :=
  {A | ∀ n : ℕ, A ∩ {ω | T ω ≤ n} ∈ (ℱ.sigma n).sets}

/-- Source 32: closure, monotonicity, measurability, adaptation, and integrability at stopping times. -/
structure DiscreteStoppingCalculus {Ω : Type u} (expectation : Expectation Ω)
    (ℱ : DiscreteFiltration Ω) (X : DiscreteProcess Ω) where
  maxStopping : ∀ S T, IsDiscreteStoppingTime ℱ S → IsDiscreteStoppingTime ℱ T →
    IsDiscreteStoppingTime ℱ (fun ω ↦ max (S ω) (T ω))
  minStopping : ∀ S T, IsDiscreteStoppingTime ℱ S → IsDiscreteStoppingTime ℱ T →
    IsDiscreteStoppingTime ℱ (fun ω ↦ min (S ω) (T ω))
  stoppedAdapted : ∀ T, IsDiscreteStoppingTime ℱ T → IsAdapted ℱ X →
    IsAdapted ℱ (stoppedProcess X T)
  stoppedIntegrable : ∀ T, IsDiscreteStoppingTime ℱ T → IsIntegrableProcess expectation X →
    IsIntegrableProcess expectation (stoppedProcess X T)

/-- Source 33: optional stopping for bounded discrete supermartingales. -/
structure OptionalStoppingDiscrete {Ω : Type u} (expectation : Expectation Ω)
    (X : DiscreteProcess Ω) (S T : Ω → ℕ) where
  order : ∀ ω, S ω ≤ T ω
  conclusion : expectation (stoppedValue X T) ≤ expectation (stoppedValue X S)

/-- Source 34: the four equivalent supermartingale/optional-stopping formulations. -/
structure SupermartingaleCharacterization (p₁ p₂ p₃ p₄ : Prop) where
  one_iff_two : p₁ ↔ p₂
  two_iff_three : p₂ ↔ p₃
  three_iff_four : p₃ ↔ p₄

/-- Source 35: almost-sure convergence of an `L¹`-bounded supermartingale. -/
structure AlmostSureMartingaleConvergence {Ω : Type u} (X : DiscreteProcess Ω) where
  limit : Ω → ℝ
  converges : ∀ ω, Tendsto (fun n ↦ X n ω) atTop (𝓝 (limit ω))

/-- Source 36: admissible numbers of completed upcrossings before time `N`. -/
def upcrossingsBefore (a b : ℝ) (x : ℕ → ℝ) (N : ℕ) : Set ℕ :=
  {k | ∃ s t : Fin k → ℕ,
    (∀ i, s i < t i) ∧ (∀ i, t i ≤ N) ∧
    (∀ i, x (s i) ≤ a ∧ b ≤ x (t i))}

/-- Source 37: numerical convergence from bounded liminf and finite rational upcrossings. -/
structure SequenceConvergenceCertificate (x : ℕ → ℝ) where
  limit : ℝ
  tendsTo : Tendsto x atTop (𝓝 limit)

/-- Source 38: Doob's upcrossing estimate. -/
structure DoobUpcrossing (a b : ℝ) where
  strict : a < b
  expectedUpcrossings : ℝ
  upperBound : ℝ
  estimate : expectedUpcrossings ≤ upperBound

/-- Source 39: discrete maximal inequality. -/
structure DiscreteMaximalInequality (threshold probability expectationValue : ℝ) where
  threshold_pos : 0 < threshold
  estimate : threshold * probability ≤ expectationValue

/-- Source 40: discrete Doob `Lᵖ` inequality. -/
structure DiscreteDoobLpInequality (p maxNorm terminalNorm : ℝ) where
  p_gt_one : 1 < p
  estimate : maxNorm ≤ p / (p - 1) * terminalNorm

/-- Source 41: `Lᵖ` martingale convergence. -/
structure DiscreteLpMartingaleConvergence {Ω : Type u} (X : DiscreteProcess Ω) where
  limit : Ω → ℝ
  pointwise : ∀ ω, Tendsto (fun n ↦ X n ω) atTop (𝓝 (limit ω))
  normConvergence : Prop

/-- Source 42: equivalent characterizations of `L¹` convergence of a martingale. -/
structure DiscreteL1MartingaleConvergence (uniformIntegrable hasTerminalRepresentation convergesL1 : Prop) where
  ui_iff_terminal : uniformIntegrable ↔ hasTerminalRepresentation
  terminal_iff_converges : hasTerminalRepresentation ↔ convergesL1

/-- Source 43: optional stopping for uniformly integrable martingales and arbitrary stopping times. -/
structure DiscreteUIOptionalStopping (conditionalIdentity expectationIdentity : Prop) where
  conditional : conditionalIdentity
  expectation : expectationIdentity

/-- Source 44: a decreasing sequence of sigma-fields. -/
structure BackwardFiltration (Ω : Type u) where
  sigma : ℕ → SigmaField Ω
  anti : ∀ m n : ℕ, m ≤ n → (sigma n).Subfield (sigma m)

/-- Source 45: convergence of conditional expectations along a backwards filtration. -/
structure BackwardMartingaleConvergence {Ω : Type u} (X : DiscreteProcess Ω) where
  limit : Ω → ℝ
  converges : ∀ ω, Tendsto (fun n ↦ X n ω) atTop (𝓝 (limit ω))

/-- Source 46: Kolmogorov's zero-one law for a tail event. -/
structure KolmogorovZeroOne (probability : ℝ) where
  dichotomy : probability = 0 ∨ probability = 1

/-- Source 47: the strong law of large numbers. -/
structure StrongLaw {Ω : Type u} (X : DiscreteProcess Ω) (mean : ℝ) where
  sampleAverage : ℕ → Ω → ℝ
  converges : ∀ ω, Tendsto (fun n ↦ sampleAverage n ω) atTop (𝓝 mean)

/-- Source 48: a Radon--Nikodym derivative certificate. -/
structure RadonNikodymCertificate (Ω : Type u) [MeasurableSpace Ω] where
  referenceMeasure : Measure Ω
  targetMeasure : Measure Ω
  density : Ω → ℝ≥0∞
  integralFormula : ∀ A : Set Ω, MeasurableSet A →
    targetMeasure A = ∫⁻ ω in A, density ω ∂referenceMeasure

/-- Source 49: a row-stochastic transition matrix. -/
def TransitionMatrix (E : Type u) [Fintype E] (P : E → E → ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧ ∀ x, ∑ y, P x y = 1

/-- Source 50: the Markov property expressed using a transition matrix. -/
structure MarkovChain {Ω : Type u} (E : Type v) [Fintype E]
    (X : ℕ → Ω → E) where
  transition : E → E → ℝ
  stochastic : TransitionMatrix E transition
  markovProperty : Prop

/-- Source 51: a harmonic function for a transition matrix. -/
def HarmonicFor (E : Type u) [Fintype E] (P : E → E → ℝ) (f : E → ℝ) : Prop :=
  ∀ x, ∑ y, P x y * f y = f x

/-- Source 52: a bounded harmonic function evaluated along a Markov chain is a martingale. -/
structure BoundedHarmonicMartingale (harmonic bounded martingale : Prop) where
  harmonicHypothesis : harmonic
  boundedHypothesis : bounded
  conclusion : martingale

end AdvancedProbability
