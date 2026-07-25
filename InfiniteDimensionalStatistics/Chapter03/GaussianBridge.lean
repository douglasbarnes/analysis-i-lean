/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.LimitClasses
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.MeasureTheory.Measure.Tight

/-!
# Chapter 3: Gaussian bridges and Donsker classes

The `P`-bridge, `P`-motion, prelinearity, pre-Gaussianity, Donsker, UPG, and
uniform-Donsker interfaces from Section 3.7.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section RandomisedProcesses

variable {Ω S : Type*}

/-- Rademacher-randomised empirical process from equation (3.272). -/
def rademacherEmpiricalProcess {n : ℕ}
    (ε : Fin n → Ω → ℝ) (X : Fin n → S)
    (𝓕 : Set (S → ℝ)) : 𝓕 → Ω → ℝ :=
  normalisedRademacherProcess ε X 𝓕

/-- Gaussian-randomised empirical process from equation (3.273). -/
def gaussianEmpiricalProcess {n : ℕ}
    (g : Fin n → Ω → ℝ) (X : Fin n → S)
    (𝓕 : Set (S → ℝ)) : 𝓕 → Ω → ℝ :=
  fun f ω ↦ (Real.sqrt (n : ℝ))⁻¹ * ∑ i, g i ω * f.1 (X i)

end RandomisedProcesses

section BridgeMetrics

variable {S : Type*} [MeasurableSpace S]

/-- Intrinsic semimetric of the `P`-Brownian bridge. -/
def brownianBridgeMetric (P : Measure S) (f g : S → ℝ) : ℝ :=
  Real.sqrt
    (brownianBridgeCovariance P (fun x ↦ f x - g x) (fun x ↦ f x - g x))

/-- Intrinsic `L²(P)` semimetric of the `P`-motion. -/
def brownianMotionMetric (P : Measure S) (f g : S → ℝ) : ℝ :=
  measureL2PseudoMetric P f g

end BridgeMetrics

section GaussianProcesses

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- A centred Gaussian process with the covariance of the `P`-bridge. -/
def IsBrownianBridge
    (P : Measure S) (𝓕 : Set (S → ℝ))
    (Q : Measure Ω) (G : 𝓕 → Ω → ℝ) : Prop :=
  ProbabilityTheory.IsGaussianProcess G Q ∧
  (∀ f, (∫ ω, G f ω ∂Q) = 0) ∧
  ∀ f g, covariance Q (G f) (G g) =
    brownianBridgeCovariance P f.1 g.1

/-- A centred Gaussian process with covariance `(f,g) ↦ P(fg)`. -/
def IsBrownianMotionIndexedBy
    (P : Measure S) (𝓕 : Set (S → ℝ))
    (Q : Measure Ω) (Z : 𝓕 → Ω → ℝ) : Prop :=
  ProbabilityTheory.IsGaussianProcess Z Q ∧
  (∀ f, (∫ ω, Z f ω ∂Q) = 0) ∧
  ∀ f g, covariance Q (Z f) (Z g) = ∫ x, f.1 x * g.1 x ∂P

/-- A process has bounded and uniformly `d`-continuous sample paths. -/
def HasBoundedUniformlyContinuousPaths {T : Type*}
    (Q : Measure Ω) (d : T → T → ℝ) (G : T → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂Q,
    (∃ M : ℝ, ∀ t, |G t ω| ≤ M) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ s t, d s t < δ → |G s ω - G t ω| < ε

/-- A concrete witness that `𝓕` is `P`-pre-Gaussian. -/
def RealisesPreGaussianClass
    (P : Measure S) (𝓕 : Set (S → ℝ))
    (Q : Measure Ω) (G : 𝓕 → Ω → ℝ) : Prop :=
  IsBrownianBridge P 𝓕 Q G ∧
  HasBoundedUniformlyContinuousPaths Q
    (fun f g ↦ brownianBridgeMetric P f.1 g.1) G

end GaussianProcesses

section Prelinearity

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/--
A map on `C` is prelinear when it respects every finite linear relation.

Source: unnumbered definition on p. 251; specification id `prelinear_map`.
-/
def IsPrelinearOn (C : Set E) (G : C → ℝ) : Prop :=
  ∀ n : ℕ, ∀ c : Fin n → C, ∀ a : Fin n → ℝ,
    (∑ i, a i • (c i).1) = 0 → ∑ i, a i * G (c i) = 0

end Prelinearity

section Donsker

variable {Ω Ω' S : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]

/-- A concrete realisation of the `P`-Donsker property. -/
def RealisesPDonskerClass
    (P : Measure S) (𝓕 : Set (S → ℝ))
    (sampleLaw : ℕ → Measure Ω)
    (ν : ℕ → 𝓕 → Ω → ℝ)
    (limitLaw : Measure Ω') (G : 𝓕 → Ω' → ℝ) : Prop :=
  RealisesPreGaussianClass P 𝓕 limitLaw G ∧
  IsDonskerProcess P (fun f ↦ f.1) sampleLaw ν limitLaw G

/-- A family of bounded-Lipschitz discrepancies tends uniformly to zero. -/
def IsUniformDonskerDiscrepancy
    {I : Type*} (d : I → ℕ → ℝ≥0∞) : Prop :=
  Tendsto (fun n ↦ ⨆ i, d i n) atTop (𝓝 0)

/-- Uniform pre-Gaussian equicontinuity over a family of indexing measures. -/
def IsUniformlyPreGaussianFor
    {I : Type*} (metric : I → (S → ℝ) → (S → ℝ) → ℝ)
    (expectedIncrementSupremum : I → ℝ → ℝ≥0∞) : Prop :=
  Tendsto (fun δ ↦ ⨆ i, expectedIncrementSupremum i δ)
    (𝓝[>] 0) (𝓝 0)

end Donsker

section SymmetricConvexClosure

variable {S : Type*} [MeasurableSpace S]

/-- Symmetric convex hull of a function class. -/
def symmetricConvexHull (𝓕 : Set (S → ℝ)) : Set (S → ℝ) :=
  convexHull ℝ (symmetricHull 𝓕)

/--
Pointwise and `L²(P)` sequential closure predicate used in `H(𝓕,P)`.
-/
def InSymmetricConvexSequentialClosure
    (P : Measure S) (𝓕 : Set (S → ℝ)) (f : S → ℝ) : Prop :=
  ∃ u : ℕ → S → ℝ,
    (∀ n, u n ∈ symmetricConvexHull 𝓕) ∧
    (∀ x, Tendsto (fun n ↦ u n x) atTop (𝓝 (f x))) ∧
    Tendsto (fun n ↦ measureL2PseudoMetric P (u n) f) atTop (𝓝 0)

/-- The class `H(𝓕,P)` from p. 257. -/
def symmetricConvexSequentialClosure
    (P : Measure S) (𝓕 : Set (S → ℝ)) : Set (S → ℝ) :=
  {f | InSymmetricConvexSequentialClosure P 𝓕 f}

end SymmetricConvexClosure

end Chapter03
end InfiniteDimensionalStatistics
