import AdvancedProbability.ContinuousTime

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u v

/-! ## 4. Weak convergence -/

/-- Source 79: the law (push-forward measure) of a random variable. -/
def law {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) : Measure E := Measure.map X μ

/-- Source 80: weak convergence against bounded continuous real test functions. -/
def WeaklyConverges {E : Type u} [MeasurableSpace E] [TopologicalSpace E]
    (μ : ℕ → Measure E) (ν : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun n ↦ ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))

/-- Source 81: the Portmanteau equivalences. -/
structure PortmanteauCertificate (weak openLower closedUpper continuitySets : Prop) where
  weak_iff_open : weak ↔ openLower
  open_iff_closed : openLower ↔ closedUpper
  closed_iff_continuity : closedUpper ↔ continuitySets

/-- Source 82: tightness of a sequence of probability measures. -/
def Tight {E : Type u} [MeasurableSpace E] [TopologicalSpace E]
    (μ : ℕ → Measure E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : Set E, IsCompact K ∧
    ∀ n, μ n (Kᶜ) ≤ ENNReal.ofReal ε

/-- Source 83: Prokhorov compactness of tight laws. -/
structure ProkhorovCertificate (tight hasWeaklyConvergentSubsequence : Prop) where
  implication : tight → hasWeaklyConvergentSubsequence

/-- Source 84: the characteristic function of a real law. -/
def characteristicFunction (μ : Measure ℝ) (t : ℝ) : ℂ :=
  ∫ x, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) ∂μ

/-- Source 85: equality of characteristic functions determines equality of laws. -/
structure CharacteristicFunctionDeterminesLaw (sameCharacteristicFunctions sameLaw : Prop) where
  implication : sameCharacteristicFunctions → sameLaw

/-- Source 86: convergence in distribution implies convergence of characteristic functions. -/
structure LevyConvergence (convergesInDistribution characteristicConvergence : Prop) where
  implication : convergesInDistribution → characteristicConvergence

/-- Source 87: Lévy's continuity theorem. -/
structure LevyContinuity (pointwiseLimit continuousAtZero convergesInDistribution : Prop) where
  limitHypothesis : pointwiseLimit
  continuityHypothesis : continuousAtZero
  conclusion : convergesInDistribution

/-- Source 88: the standard characteristic-function tail bound. -/
structure CharacteristicTailBound (tailProbability integralBound : ℝ) where
  estimate : tailProbability ≤ integralBound

end AdvancedProbability
