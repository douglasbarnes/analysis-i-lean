/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.VapnikChervonenkis

/-!
# Chapter 3: Weak convergence and Donsker interfaces

Definitions for bounded-Lipschitz convergence, covariance kernels,
asymptotic equicontinuity and Donsker classes.  These declarations formalise
the objects used in Sections 3.6–3.7 without asserting the deep convergence
theorems before they are proved.
-/

noncomputable section

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter

namespace InfiniteDimensionalStatistics
namespace Chapter03

section BoundedLipschitz

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

/-- Unit bounded-Lipschitz class. -/
def boundedLipschitzClass : Set (E → ℝ) :=
  {f | LipschitzWith 1 f ∧ ∀ x, |f x| ≤ 1}

/-- Extended bounded-Lipschitz distance between finite measures. -/
def boundedLipschitzDistance (P Q : Measure E) : ℝ≥0∞ :=
  ⨆ f : boundedLipschitzClass (E := E),
    ENNReal.ofReal |(∫ x, f.1 x ∂P) - ∫ x, f.1 x ∂Q|

/-- Weak convergence expressed through bounded-Lipschitz distance. -/
def WeaklyConverges (P : ℕ → Measure E) (Q : Measure E) : Prop :=
  Tendsto (fun n ↦ boundedLipschitzDistance (P n) Q) atTop (𝓝 0)

end BoundedLipschitz

section Covariance

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- Covariance of two real random variables. -/
def covariance (P : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  ∫ ω,
    (X ω - ∫ u, X u ∂P) * (Y ω - ∫ u, Y u ∂P) ∂P

/-- Covariance kernel of the `P`-Brownian bridge indexed by functions. -/
def brownianBridgeCovariance (P : Measure S) (f g : S → ℝ) : ℝ :=
  (∫ x, f x * g x ∂P) - (∫ x, f x ∂P) * ∫ x, g x ∂P

/-- A process has the Brownian-bridge covariance prescribed by `P`. -/
def HasBrownianBridgeCovariance {T : Type*} (P : Measure S)
    (index : T → S → ℝ) (Q : Measure Ω) (G : T → Ω → ℝ) : Prop :=
  ∀ s t, covariance Q (G s) (G t) =
    brownianBridgeCovariance P (index s) (index t)

end Covariance

section Equicontinuity

variable {T Ω : Type*} [MeasurableSpace Ω]

/-- Extended supremum of process increments over pairs at distance at most `δ`. -/
def processIncrementSupremum (d : T → T → ℝ)
    (X : T → Ω → ℝ) (δ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ s : T, ⨆ t : T,
    if d s t ≤ δ then ENNReal.ofReal |X s ω - X t ω| else 0

/-- Finite-sample asymptotic equicontinuity in outer probability. -/
def AsymptoticallyEquicontinuous
    (P : ℕ → Measure Ω) (d : T → T → ℝ)
    (X : ℕ → T → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∀ η > 0,
    ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
      P n {ω | ENNReal.ofReal ε < processIncrementSupremum d (X n) δ ω} ≤
        ENNReal.ofReal η

end Equicontinuity

section Donsker

variable {S T Ω Ω' : Type*}
  [MeasurableSpace S] [PseudoMetricSpace (T → ℝ)] [MeasurableSpace (T → ℝ)]
  [MeasurableSpace Ω] [MeasurableSpace Ω']

/--
A function-indexed process sequence is Donsker when its laws converge weakly to
a measurable limit process with the Brownian-bridge covariance.
-/
def IsDonskerProcess (P : Measure S) (index : T → S → ℝ)
    (sampleLaw : ℕ → Measure Ω) (X : ℕ → T → Ω → ℝ)
    (limitLaw : Measure Ω') (G : T → Ω' → ℝ) : Prop :=
  (∀ n, Measurable fun ω t ↦ X n t ω) ∧
    Measurable (fun ω t ↦ G t ω) ∧
    HasBrownianBridgeCovariance P index limitLaw G ∧
    WeaklyConverges
      (fun n ↦ Measure.map (fun ω t ↦ X n t ω) (sampleLaw n))
      (Measure.map (fun ω t ↦ G t ω) limitLaw)

end Donsker

end Chapter03
end InfiniteDimensionalStatistics
