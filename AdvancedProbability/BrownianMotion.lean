import AdvancedProbability.WeakConvergence

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u v

/-! ## 5. Brownian motion -/

/-- Gaussianity expressed by the real and imaginary parts of the characteristic function. -/
def HasGaussianLaw {Ω : Type u} (expectation : Expectation Ω) (X : Ω → ℝ)
    (mean variance : ℝ) : Prop :=
  ∀ t : ℝ,
    expectation (fun ω ↦ Real.cos (t * X ω)) =
        Real.exp (-(variance * t ^ 2) / 2) * Real.cos (mean * t) ∧
      expectation (fun ω ↦ Real.sin (t * X ω)) =
        Real.exp (-(variance * t ^ 2) / 2) * Real.sin (mean * t)

/-- Source 89: standard one-dimensional Brownian motion. -/
structure BrownianMotion (Ω : Type u) (expectation : Expectation Ω)
    (independentRelation : (Ω → ℝ) → (Ω → ℝ) → Prop) where
  path : ContinuousProcess Ω
  startsAtZero : ∀ ω, path 0 ω = 0
  continuousPaths : IsContinuousProcess path
  gaussianIncrements : ∀ s t : ℝ≥0, s ≤ t →
    HasGaussianLaw expectation (fun ω ↦ path t ω - path s ω) 0 ((t - s : ℝ≥0) : ℝ)
  independentIncrements : ∀ r s t : ℝ≥0, r ≤ s → s ≤ t →
    independentRelation (fun ω ↦ path s ω - path r ω) (fun ω ↦ path t ω - path s ω)

/-- Source 90: an existence certificate for Brownian motion. -/
structure WienerExistence where
  Ω : Type u
  expectation : Expectation Ω
  independent : (Ω → ℝ) → (Ω → ℝ) → Prop
  brownian : BrownianMotion Ω expectation independent

/-- Source 94: Blumenthal's zero-one law. -/
structure BlumenthalZeroOne (probability : ℝ) where
  dichotomy : probability = 0 ∨ probability = 1

/-- Source 95: immediate oscillation, small-time behavior, and unbounded extrema of Brownian paths. -/
structure BrownianSamplePathProperties (immediatePositive immediateNegative smallTimeRatio
    unboundedAbove unboundedBelow : Prop) where
  p1 : immediatePositive
  p2 : immediateNegative
  p3 : smallTimeRatio
  p4 : unboundedAbove
  p5 : unboundedBelow

/-- Source 96: the strong Markov property of Brownian motion. -/
structure BrownianStrongMarkov (postStoppingBrownian independentOfStoppedPast : Prop) where
  law : postStoppingBrownian
  independence : independentOfStoppedPast

/-- Source 97: the reflection principle. -/
structure ReflectionPrinciple (reflectedPathHasBrownianLaw : Prop) where
  conclusion : reflectedPathHasBrownianLaw

/-- Source 98: first-passage reflection identity. -/
structure ReflectionHittingCorollary (hittingProbability doubledTailProbability : ℝ) where
  identity : hittingProbability = doubledTailProbability

/-- Source 99: the running maximum has the same law as the absolute Brownian position. -/
structure RunningMaximumLaw (sameLaw : Prop) where
  conclusion : sameLaw

/-- Source 100: one-dimensional Brownian first-passage probability and density data. -/
structure BrownianFirstPassage (distributionIdentity densityIdentity : Prop) where
  distribution : distributionIdentity
  density : densityIdentity

/-- Source 101: an open connected subset of Euclidean space. -/
def Domain (d : ℕ) (D : Set (Fin d → ℝ)) : Prop := IsOpen D ∧ IsConnected D

/-- Source 102: harmonicity through vanishing Laplacian, represented by a supplied Laplacian. -/
def IsHarmonic {E : Type u} (laplacian : (E → ℝ) → E → ℝ) (D : Set E) (u : E → ℝ) : Prop :=
  ∀ x, x ∈ D → laplacian u x = 0

/-- Source 103: equivalence of harmonicity and the mean-value property. -/
structure MeanValueCharacterization (harmonic meanValueProperty : Prop) where
  equivalence : harmonic ↔ meanValueProperty

/-- Source 104: a harmonic function evaluated along Brownian motion is a martingale. -/
structure HarmonicBrownianMartingale (harmonic martingale : Prop) where
  implication : harmonic → martingale

/-- Source 106: the second-order Taylor/Itô martingale for Brownian motion. -/
structure ItoMartingale (twiceDifferentiable boundedDerivatives martingale : Prop) where
  smooth : twiceDifferentiable
  bounded : boundedDerivatives
  conclusion : martingale

/-- Source 107: the weak maximum-principle property for a domain and a supplied Laplacian.
Every harmonic function continuous on the closure and bounded above by `c` on the frontier is
bounded above by `c` throughout the domain. -/
def MaximumPrinciple {E : Type u} [TopologicalSpace E]
    (laplacian : (E → ℝ) → E → ℝ) (D : Set E) : Prop :=
  ∀ (u : E → ℝ), IsHarmonic laplacian D u → ContinuousOn u (closure D) →
    ∀ c : ℝ, (∀ x, x ∈ frontier D → u x ≤ c) → ∀ x, x ∈ D → u x ≤ c

/-- Source 109: the Poincaré exterior-cone condition. -/
def PoincareConeCondition {E : Type u} [TopologicalSpace E]
    (D : Set E) (HasExteriorCone : E → Prop) : Prop :=
  ∀ x, x ∈ frontier D → HasExteriorCone x

/-- Source 110: a uniform positive probability of hitting an open cone before leaving a ball. -/
structure ConeHittingEstimate (probability lowerBound : ℝ) where
  lowerBound_nonnegative : 0 ≤ lowerBound
  estimate : lowerBound ≤ probability

/-- Source 111: Brownian representation solves the Dirichlet problem on cone-regular domains. -/
structure BrownianDirichletSolution (boundaryContinuous harmonic continuousExtension : Prop) where
  boundaryHypothesis : boundaryContinuous
  harmonicConclusion : harmonic
  continuityConclusion : continuousExtension

/-- Source 112: recurrence in dimensions one and two and transience in dimensions at least three. -/
def BrownianRecurrenceTransience (d : ℕ) : Prop := (d ≤ 2) ∨ (3 ≤ d)

/-- Source 113: Donsker's invariance principle. -/
structure DonskerInvariance (centered unitVariance weakConvergenceToBrownian : Prop) where
  centeredHypothesis : centered
  varianceHypothesis : unitVariance
  conclusion : weakConvergenceToBrownian

/-- Source 114: Skorokhod embedding of a centered finite-variance law in Brownian motion. -/
structure SkorokhodEmbedding (centered finiteVariance embeddedRandomWalk : Prop) where
  centeredHypothesis : centered
  varianceHypothesis : finiteVariance
  conclusion : embeddedRandomWalk

/-- Source 115: two-sided Brownian exit probability and mean exit time. -/
structure TwoSidedHittingFormula (x y probability expectedTime : ℝ) where
  x_pos : 0 < x
  y_pos : 0 < y
  probabilityFormula : probability = y / (x + y)
  expectationFormula : expectedTime = x * y

end AdvancedProbability
